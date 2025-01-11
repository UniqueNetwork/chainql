use client::{dump::ClientDump, live::ClientShared, Client, ClientT};
use directories::BaseDirs;
use frame_metadata::{
	PalletMetadata, RuntimeMetadata, RuntimeMetadataPrefixed, RuntimeMetadataV14,
	StorageEntryModifier, StorageEntryType, StorageHasher,
};
use hex::{builtin_from_hex, builtin_to_hex, Hex};
use jrsonnet_evaluator::{
	bail,
	error::{Error as JrError, Result},
	function::builtin,
	runtime_error,
	typed::{Either2, NativeFn, Typed},
	val::{ArrValue, ThunkValue},
	ContextInitializer, Either, IStr, ObjValue, ObjValueBuilder, Pending, ResultExt, State, Thunk,
	Val,
};
use jrsonnet_gcmodule::Trace;
use num_bigint::BigInt;
use parity_scale_codec::{Compact, Decode, Encode, Input, Output};
use rebuild::rebuild;
use scale_info::{
	form::PortableForm, interner::UntrackedSymbol, Field, PortableRegistry, TypeDef,
	TypeDefPrimitive,
};
use serde::Deserialize;
use sp_core::{
	blake2_128, blake2_256, crypto::Ss58Codec, storage::StateVersion, twox_128, twox_256, twox_64,
	ByteArray, U256,
};
use sp_io::{hashing::keccak_256, trie::blake2_256_root};
use std::sync::Arc;
use std::{
	any::TypeId,
	collections::{BTreeMap, BTreeSet, HashSet},
	path::PathBuf,
	rc::Rc,
	str::FromStr,
};
use tokio::sync::Notify;
use wasm::{builtin_runtime_wasm, RuntimeContainer};

use crate::address::{verify_signature, AddressSchema, AddressType, Ss58Format};

use self::{
	address::{
		builtin_address_seed, builtin_ecdsa_address_seed, builtin_ecdsa_seed,
		builtin_ed25519_address_seed, builtin_ed25519_seed, builtin_ethereum_address_seed,
		builtin_ethereum_seed, builtin_seed, builtin_sr25519_address_seed, builtin_sr25519_seed,
		SignatureType,
	},
	ethereum::builtin_eth_encode,
};

pub mod address;
mod client;
pub mod ethereum;
pub mod hex;
pub mod rebuild;
pub mod wasm;
mod log;

/// Translate metadata into Jrsonnet's Val.
fn metadata_obj(meta: &RuntimeMetadataV14) -> Val {
	let ty = serde_json::to_value(meta).expect("valid value");
	Val::deserialize(ty).expect("valid value")
}

/// Create a lazily-evaluated thunk by wrapping the call inside.
macro_rules! simple_thunk {
    (
        $(
            $(#[trace($meta:meta)])?
            let $name:ident: $ty:ty = $expr:expr;
        )*
        Thunk::<$out:ty>::evaluated($val:expr)
    ) => {{
        #[derive(Trace)]
        struct InvisThunk {
            $(
                $(#[trace($meta)])?
                $name: $ty
            ),*
        }
        impl ThunkValue for InvisThunk {
            type Output = $out;

            fn get(self: Box<Self>) -> Result<Self::Output> {
                let Self {$($name),*} = *self;
                Ok($val)
            }
        }

        #[allow(clippy::redundant_field_names)]
        Thunk::new(InvisThunk {
            $($name: $expr,)*
        })
    }};
}

/// Return an Err from a formatted string if the condition is not met.
#[macro_export]
macro_rules! ensure {
    ($cond:expr, $($tt:tt)+) => {
        if !($cond) {
            jrsonnet_evaluator::bail!($($tt)+)
        }
    };
}

/// Return a missing resolve error.
fn missing_resolve() -> JrError {
	runtime_error!("invalid metadata: missing resolve key")
}

/// Return a codec error.
fn codec_error(err: parity_scale_codec::Error) -> JrError {
	runtime_error!("codec: {}", err)
}

/// Decode a value as it is or into compact.
fn decode_maybe_compact<I, T>(dec: &mut I, compact: bool) -> Result<T>
where
	I: Input,
	T: Decode,
	Compact<T>: Decode,
{
	if compact {
		<Compact<T>>::decode(dec).map(|v| v.0).map_err(codec_error)
	} else {
		T::decode(dec).map_err(codec_error)
	}
}

/// Encode a value as it is or into compact, adding the output to [`dest`].
fn encode_maybe_compact<T, O>(compact: bool, val: T, dest: &mut O)
where
	T: Encode,
	O: Output,
	Compact<T>: Encode,
{
	if compact {
		Compact(val).encode_to(dest)
	} else {
		val.encode_to(dest)
	}
}

/// Encode the contents of an object according to the supplied types [`typ`] into [`Val`], adding it to [`out`].
fn encode_obj_value<O>(
	reg: &PortableRegistry,
	typ: &[Field<PortableForm>],
	compact: bool,
	val: Val,
	out: &mut O,
) -> Result<()>
where
	O: Output,
{
	if typ.len() == 1 {
		return encode_value(reg, typ[0].ty, compact, val, out, false);
	}
	let val = ObjValue::from_untyped(val)?;
	for (i, f) in typ.iter().enumerate() {
		let field_name: IStr = f
			.name
			.clone()
			.unwrap_or_else(|| format!("unnamed{}", i))
			.into();
		State::push_description(
			|| format!(".{field_name}"),
			|| {
				let field = val
					.get(field_name.clone())?
					.ok_or_else(|| runtime_error!("missing field {field_name}"))?;
				encode_value(reg, f.ty, compact, field, out, false)?;
				Ok(())
			},
		)?;
	}
	Ok(())
}

/// Decode the contents of an object according to the supplied types [`typ`].
fn decode_obj_value<I>(
	dec: &mut I,
	reg: &PortableRegistry,
	typ: &[Field<PortableForm>],
	compact: bool,
) -> Result<Val>
where
	I: Input,
{
	if typ.len() == 1 {
		return decode_value(dec, reg, typ[0].ty, compact);
	}
	let mut out = ObjValueBuilder::new();
	for (i, f) in typ.iter().enumerate() {
		let field = decode_value(dec, reg, f.ty, compact)?;
		out.field(f.name.clone().unwrap_or_else(|| format!("unnamed{}", i)))
			.try_value(field)?;
	}
	Ok(Val::Obj(out.build()))
}

/// Unpack a complex or wrapping type into the type it wraps.
fn extract_newtypes(
	reg: &PortableRegistry,
	typ: UntrackedSymbol<TypeId>,
	compact: bool,
) -> Result<(bool, UntrackedSymbol<TypeId>)> {
	match &reg.resolve(typ.id).ok_or_else(missing_resolve)?.type_def {
		TypeDef::Composite(c) if c.fields.len() == 1 => {
			extract_newtypes(reg, c.fields[0].ty, compact)
		}
		TypeDef::Array(a) if a.len == 1 => extract_newtypes(reg, a.type_param, compact),
		TypeDef::Tuple(d) if d.fields.len() == 1 => extract_newtypes(reg, d.fields[0], compact),
		TypeDef::Compact(c) => extract_newtypes(reg, c.type_param, true),
		_ => Ok((compact, typ)),
	}
}

/// Parse a value generated from a string into JSON.
fn maybe_json_parse(v: Val, from_string: bool) -> Result<Val> {
	if !from_string {
		return Ok(v);
	}
	if let Some(str) = v.as_str() {
		let value: Val = serde_json::from_str(&str).map_err(|e| runtime_error!("json: {e}"))?;
		Ok(value)
	} else {
		Ok(v)
	}
}

fn bigint_encode<T: FromStr>(v: Val) -> Result<T>
where
	T::Err: std::fmt::Display,
{
	let v = match v {
		Val::BigInt(n) => (*n).clone(),
		Val::Str(v) => {
			BigInt::from_str(&v.to_string()).map_err(|e| runtime_error!("bigint parse: {e}"))?
		}
		_ => bail!("unexpected type for bigint decoder: {}", v.value_type()),
	};
	v.to_string()
		.parse()
		.map_err(|e| runtime_error!("bigint encode: {e}"))
}
fn bigint_decode<T: std::fmt::Display>(v: T) -> Result<Val> {
	let v = v.to_string();
	let v: BigInt = v
		.parse()
		.map_err(|e| runtime_error!("bigint decode: {e}"))?;
	Ok(Val::BigInt(Box::new(v)))
}
/// Encode a value [`val`] according to the type [`typ`] registered in the [`reg`], adding it to [`out`].
fn encode_value<O>(
	reg: &PortableRegistry,
	mut typ: UntrackedSymbol<TypeId>,
	mut compact: bool,
	val: Val,
	out: &mut O,
	from_string: bool,
) -> Result<()>
where
	O: Output,
{
	let (new_compact, new_typ) = extract_newtypes(reg, typ, compact)?;
	compact = new_compact;
	typ = new_typ;
	match &reg.resolve(typ.id).ok_or_else(missing_resolve)?.type_def {
		TypeDef::Composite(comp) => {
			let val = maybe_json_parse(val, from_string)?;
			encode_obj_value(reg, &comp.fields, compact, val, out)?;
		}
		TypeDef::Variant(e) => {
			if let Some(str) = val.as_str() {
				for variant in e.variants.iter() {
					if variant.name.as_str() == str.as_str() && variant.fields.is_empty() {
						variant.index.encode_to(out);
						return Ok(());
					}
				}
			}
			let val = maybe_json_parse(val, from_string)?;
			let v = ObjValue::from_untyped(val)?;
			let name = &v.fields(true);
			ensure!(name.len() == 1, "not a enum");
			let name = name[0].clone();
			let value = v
				.get(name.clone())?
				.expect("value exists, as name is obtained from .fields()");

			for variant in e.variants.iter() {
				if variant.name.as_str() == name.as_str() {
					variant.index.encode_to(out);
					return encode_obj_value(reg, &variant.fields, compact, value, out);
				}
			}
			bail!("variant not found: {name}");
		}
		TypeDef::Sequence(e) => {
			if matches!(
				reg.resolve(e.type_param.id)
					.ok_or_else(missing_resolve)?
					.type_def,
				TypeDef::Primitive(TypeDefPrimitive::U8)
			) {
				let raw = Hex::from_untyped(val)?;
				raw.encode_to(out);
				return Ok(());
			}
			let val = maybe_json_parse(val, from_string)?;
			let v = Vec::<Val>::from_untyped(val)?;
			Compact(v.len() as u32).encode_to(out);
			for val in v.iter() {
				encode_value(reg, e.type_param, compact, val.clone(), out, false)?;
			}
		}
		TypeDef::Array(e) => {
			if matches!(
				reg.resolve(e.type_param.id)
					.ok_or_else(missing_resolve)?
					.type_def,
				TypeDef::Primitive(TypeDefPrimitive::U8)
			) {
				let raw = Hex::from_untyped(val)?;
				ensure!(
					e.len as usize == raw.len(),
					"array has wrong number for elements, expected {}, got {}",
					e.len,
					raw.len()
				);
				for i in &*raw {
					i.encode_to(out);
				}
				return Ok(());
			}
			let val = maybe_json_parse(val, from_string)?;
			let v = Vec::<Val>::from_untyped(val)?;
			ensure!(
				e.len as usize == v.len(),
				"array has wrong number of elements, expected {}, got {}",
				e.len,
				v.len(),
			);
			for val in v.iter() {
				encode_value(reg, e.type_param, compact, val.clone(), out, false)?;
			}
		}
		TypeDef::Tuple(e) => {
			let val = maybe_json_parse(val, from_string)?;
			let v = ArrValue::from_untyped(val)?;
			ensure!(
				e.fields.len() == v.len(),
				"tuple has wrong number of elements"
			);
			for (ty, val) in e.fields.iter().zip(v.iter()) {
				let val = val?;
				encode_value(reg, *ty, compact, val.clone(), out, false)?;
			}
		}
		TypeDef::Primitive(p) => match p {
			TypeDefPrimitive::Bool => {
				let val = maybe_json_parse(val, from_string)?;
				let b = bool::from_untyped(val)?;
				b.encode_to(out)
			}
			TypeDefPrimitive::Char => bail!("char not supported"),
			TypeDefPrimitive::Str => {
				let s = String::from_untyped(val)?;
				s.encode_to(out)
			}
			TypeDefPrimitive::U8 => {
				let val = maybe_json_parse(val, from_string)?;
				let v = u8::from_untyped(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::U16 => {
				let val = maybe_json_parse(val, from_string)?;
				let v = u16::from_untyped(val)?;
				encode_maybe_compact::<u16, _>(compact, v, out)
			}
			TypeDefPrimitive::U32 => {
				let val = maybe_json_parse(val, from_string)?;
				let v = u32::from_untyped(val)?;
				encode_maybe_compact::<u32, _>(compact, v, out)
			}
			TypeDefPrimitive::U64 => {
				let v = bigint_encode(val)?;
				encode_maybe_compact::<u64, _>(compact, v, out)
			}
			TypeDefPrimitive::U128 => {
				let v = bigint_encode(val)?;
				encode_maybe_compact::<u128, _>(compact, v, out)
			}
			TypeDefPrimitive::U256 => {
				ensure!(!compact, "U256 can't be compact");
				let v: U256 = bigint_encode(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I8 => {
				let val = maybe_json_parse(val, from_string)?;
				let v = i8::from_untyped(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I16 => {
				let val = maybe_json_parse(val, from_string)?;
				ensure!(!compact, "int can't be compact");
				let v = i16::from_untyped(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I32 => {
				let val = maybe_json_parse(val, from_string)?;
				ensure!(!compact, "int can't be compact");
				let v = i32::from_untyped(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I64 => {
				ensure!(!compact, "int can't be compact");
				let v: i64 = bigint_encode(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I128 => {
				ensure!(!compact, "int can't be compact");
				let v: i128 = bigint_encode(val)?;
				v.encode_to(out)
			}
			TypeDefPrimitive::I256 => {
				bail!("i256 not supported");
			}
		},
		TypeDef::Compact(_) => encode_value(reg, typ, true, val, out, from_string)?,
		TypeDef::BitSequence(_) => bail!("bitseq not supported"),
	}
	Ok(())
}

/// Decode some value [`dec`] into the type [`typ`] in the registry [`reg`].
fn decode_value<I>(
	dec: &mut I,
	reg: &PortableRegistry,
	mut typ: UntrackedSymbol<TypeId>,
	mut compact: bool,
) -> Result<Val>
where
	I: Input,
{
	let (new_compact, new_typ) = extract_newtypes(reg, typ, compact)?;
	compact = new_compact;
	typ = new_typ;
	Ok(
		match &reg.resolve(typ.id).ok_or_else(missing_resolve)?.type_def {
			TypeDef::Composite(c) => decode_obj_value(dec, reg, &c.fields, compact)?,
			TypeDef::Variant(e) => {
				let idx = u8::decode(dec).map_err(codec_error)?;
				for var in e.variants.iter() {
					if var.index == idx {
						if var.fields.is_empty() {
							return Ok(Val::string(var.name.as_str()));
						}
						let mut obj = ObjValueBuilder::new();
						let val = decode_obj_value(dec, reg, &var.fields, compact)?;
						obj.field(var.name.as_str()).try_value(val)?;

						return Ok(Val::Obj(obj.build()));
					}
				}
				bail!("invalid metadata: missing variant")
			}
			TypeDef::Sequence(seq) => {
				if matches!(
					reg.resolve(seq.type_param.id)
						.ok_or_else(missing_resolve)?
						.type_def,
					TypeDef::Primitive(TypeDefPrimitive::U8)
				) {
					let raw = <Vec<u8>>::decode(dec).map_err(codec_error)?;
					return Hex::into_untyped(Hex(raw.as_slice().into()));
				}

				let mut out = vec![];
				let size = <Compact<u32>>::decode(dec).map_err(codec_error)?;
				for _ in 0..size.0 {
					let val = decode_value(dec, reg, seq.type_param, compact)?;
					out.push(val);
				}
				Val::Arr(ArrValue::eager(out))
			}
			TypeDef::Array(arr) => {
				if matches!(
					reg.resolve(arr.type_param.id)
						.ok_or_else(missing_resolve)?
						.type_def,
					TypeDef::Primitive(TypeDefPrimitive::U8)
				) {
					let mut raw = vec![0; arr.len as usize];
					for v in raw.iter_mut() {
						*v = u8::decode(dec).expect("byte");
					}
					return Hex::into_untyped(Hex(raw.as_slice().into()));
				}

				let mut out = vec![];
				for _ in 0..arr.len {
					let val = decode_value(dec, reg, arr.type_param, compact)?;
					out.push(val);
				}
				Val::Arr(ArrValue::eager(out))
			}
			TypeDef::Tuple(t) => {
				let mut out = Vec::with_capacity(t.fields.len());
				for t in t.fields.iter() {
					let val = decode_value(dec, reg, *t, compact)?;
					out.push(val);
				}
				Val::Arr(ArrValue::eager(out))
			}
			TypeDef::Primitive(p) => match p {
				TypeDefPrimitive::Bool => {
					let val = bool::decode(dec).map_err(codec_error)?;
					Val::Bool(val)
				}
				TypeDefPrimitive::Char => bail!("char not supported"),
				TypeDefPrimitive::Str => {
					let val = String::decode(dec).map_err(codec_error)?;
					Val::string(val)
				}
				TypeDefPrimitive::U8 => {
					let val = u8::decode(dec).map_err(codec_error)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::U16 => {
					let val = decode_maybe_compact::<_, u16>(dec, compact)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::U32 => {
					let val = decode_maybe_compact::<_, u32>(dec, compact)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::U64 => {
					let val = decode_maybe_compact::<_, u64>(dec, compact)?;
					Val::string(val.to_string())
				}
				TypeDefPrimitive::U128 => {
					let val = decode_maybe_compact::<_, u128>(dec, compact)?;
					bigint_decode(val)?
				}
				TypeDefPrimitive::U256 => {
					ensure!(!compact, "u256 can't be compact");
					let val = U256::decode(dec).map_err(codec_error)?;
					bigint_decode(val)?
				}
				TypeDefPrimitive::I8 => {
					let val = i8::decode(dec).map_err(codec_error)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::I16 => {
					ensure!(!compact, "int can't be compact");
					let val = i16::decode(dec).map_err(codec_error)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::I32 => {
					ensure!(!compact, "int can't be compact");
					let val = i32::decode(dec).map_err(codec_error)?;
					Val::Num(val.into())
				}
				TypeDefPrimitive::I64 => {
					ensure!(!compact, "int can't be compact");
					let val = i64::decode(dec).map_err(codec_error)?;
					bigint_decode(val)?
				}
				TypeDefPrimitive::I128 => {
					ensure!(!compact, "int can't be compact");
					let val = i128::decode(dec).map_err(codec_error)?;
					bigint_decode(val)?
				}
				TypeDefPrimitive::I256 => {
					bail!("i256 not supported");
				}
			},
			TypeDef::Compact(c) => decode_value(dec, reg, c.type_param, true)?,
			TypeDef::BitSequence(_) => bail!("bitseq not supported"),
		},
	)
}

/// Fetch some value under a key in the storage and decode it according to the type [`typ`], or optionally use a default if the decoding fails.
fn fetch_decode_key(
	key: &[u8],
	client: Client,
	registry: Rc<PortableRegistry>,
	typ: UntrackedSymbol<TypeId>,
	default: Option<Vec<u8>>,
) -> Result<Val> {
	let value = client.get_storage(key)?;
	Ok(if let Some(value) = value {
		decode_value(&mut &value[..], &registry, typ, false)?
	} else if let Some(default) = default {
		decode_value(&mut &default[..], &registry, typ, false)?
	} else {
		unreachable!("unknown keys should not be present")
	})
}

/// Contains all the necessary data for correct loading of and decoding keys, uniformly accessed by entries' thunks.
struct SharedMapFetcherContext {
	client: Client,
	reg: Rc<PortableRegistry>,
	fetched: Vec<Vec<u8>>,
	keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)>,
	value_typ: UntrackedSymbol<TypeId>,
	value_default: Option<Vec<u8>>,
	opts: ChainOpts,
}

/// Contains smart pointers to shared data to be accessed by entries' thunks, together with the pointer to own latest key depth.
#[derive(Clone)]
struct MapFetcherContext {
	shared: Rc<SharedMapFetcherContext>,
	prefix: Rc<Vec<u8>>,
	current_key_depth: usize,
}

impl MapFetcherContext {
	/// Get the latest key.
	fn key(&self) -> Option<&(StorageHasher, UntrackedSymbol<TypeId>)> {
		self.shared.keys.get(self.current_key_depth)
	}
}

/// Cache and objectify all keys from the fetched and return the resulting cache.
fn make_fetched_keys_storage(c: MapFetcherContext) -> Result<Val> {
	let key = if let Some(k) = c.key() {
		k
	} else {
		// TODO: bulk fetching for last key and assert!(!keys.is_empty())
		return fetch_decode_key(
			&c.prefix,
			c.shared.client.clone(),
			c.shared.reg.clone(),
			c.shared.value_typ,
			c.shared.value_default.clone(),
		);
	};
	let hash_bytes = match key.0 {
		StorageHasher::Blake2_128Concat => Ok(128 / 8),
		StorageHasher::Twox64Concat => Ok(64 / 8),
		StorageHasher::Identity => Ok(0),
		StorageHasher::Blake2_128 => Err(128 / 8),
		StorageHasher::Blake2_256 => Err(256 / 8),
		StorageHasher::Twox128 => Err(128 / 8),
		StorageHasher::Twox256 => Err(256 / 8),
	};
	let key_ty = key.1;
	let mut out = ObjValueBuilder::new();
	let mut keyout = ObjValueBuilder::new();
	let pending_out = Pending::<ObjValue>::new();
	let mut visited_prefixes = HashSet::new();
	for key in &c.shared.fetched {
		if !key.starts_with(&c.prefix) {
			continue;
		}
		let key = &key[c.prefix.len()..];
		let mut prefix = c.prefix.to_vec();
		prefix.extend_from_slice(&key[..hash_bytes.unwrap_or(0)]);
		let mut key = &key[hash_bytes.unwrap_or(0)..];
		let orig_key = key;
		let key_plus_value_len = key.len();
		let value = if let Err(e) = hash_bytes {
			let mut bytes = vec![0u8; e];
			bytes.copy_from_slice(&key[..e]);
			key = &key[e..];
			Hex::into_untyped(Hex(bytes))?
		} else {
			decode_value(&mut key, &c.shared.reg, key_ty, false)?
		};
		// dbg!(&value);
		let value_len = key_plus_value_len - key.len();

		if visited_prefixes.contains(&orig_key[..value_len]) {
			continue;
		}
		visited_prefixes.insert(&orig_key[..value_len]);

		prefix.extend_from_slice(&orig_key[..value_len]);
		let value = if let Some(str) = value.as_str() {
			str
		} else {
			value.to_string()?
		};
		keyout
			.field(value.clone())
			.try_value(Hex::into_untyped(Hex(prefix.clone()))?)?;

		if c.current_key_depth + 1 == c.shared.keys.len() {
			// Next value is not submap
			// Optional values have no map entry by convention, so we skip this key even when !include_defaults
			let should_have_entry = c.shared.opts.include_defaults
				&& c.shared.value_default.is_some()
				|| c.shared.client.contains_key(&prefix)?;
			if !should_have_entry {
				continue;
			}
		} else {
			// Submap
			// Optional values have no map entry by convention, so we skip this key even when !include_defaults
			let should_have_entry = c.shared.opts.include_defaults
				&& c.shared.value_default.is_some()
				|| c.shared.client.contains_data_for(&prefix)?;
			if !should_have_entry {
				continue;
			}
		}
		let c = MapFetcherContext {
			shared: c.shared.clone(),
			prefix: Rc::new(prefix),
			current_key_depth: c.current_key_depth + 1,
		};
		let bound = simple_thunk! {
			#[trace(skip)]
			let c: MapFetcherContext = c;
			Thunk::<Val>::evaluated(make_fetched_keys_storage(c)?)
		};
		out.field(value.clone()).thunk(bound)?;
	}
	let preload_keys = simple_thunk! {
		let shared: Rc<SharedMapFetcherContext> = c.shared;
		let prefix: Rc<Vec<u8>> = c.prefix;
		let pending_out: Pending<ObjValue> = pending_out.clone();
		Thunk::<Val>::evaluated({
			eprintln!("preloading subset of keys by prefix: {prefix:0>2x?}");
			let prefixes = shared.fetched.iter().filter(|k| k.starts_with(&prefix)).collect::<Vec<_>>();
			shared.client.preload_storage(prefixes.as_slice())?;
			Val::Obj(pending_out.unwrap())
		})
	};
	out.field("_preloadKeys").hide().thunk(preload_keys)?;
	out.field("_key").hide().try_value(keyout.build())?;
	let out = out.build();
	pending_out.fill(out.clone());
	Ok(Val::Obj(out))
}

/// Fetch keys of some storage and cache them, returning the resulting cache value.
fn make_fetch_keys_storage(
	client: Client,
	prefix: Vec<u8>,
	reg: Rc<PortableRegistry>,
	keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)>,
	value_typ: UntrackedSymbol<TypeId>,
	value_default: Option<Vec<u8>>,
	opts: ChainOpts,
) -> Result<Val> {
	let fetched = client.get_keys(prefix.as_slice())?;
	make_fetched_keys_storage(MapFetcherContext {
		shared: Rc::new(SharedMapFetcherContext {
			client,
			reg,
			fetched,
			keys,
			value_typ,
			value_default,
			opts,
		}),
		prefix: Rc::new(prefix),
		current_key_depth: 0,
	})
}

/// Create a Jsonnet object out of given pallets' storage and assign appropriate methods.
fn make_pallet_key(
	client: Client,
	data: PalletMetadata<PortableForm>,
	registry: Rc<PortableRegistry>,
	opts: ChainOpts,
) -> Result<ObjValue> {
	let mut out = ObjValueBuilder::new();
	let mut keyout = ObjValueBuilder::new();
	let mut encode_keyout = ObjValueBuilder::new();
	let mut encode_valueout = ObjValueBuilder::new();
	let mut decode_valueout = ObjValueBuilder::new();
	let mut key_args = ObjValueBuilder::new();
	let Some(storage) = data.storage else {
		unreachable!("pallets with no storage are not added to the state map");
	};
	let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
	let mut known_prefixes = Vec::new();
	for entry in storage.entries {
		let key_key = sp_core::twox_128(entry.name.as_bytes());
		let mut entry_key = vec![];
		entry_key.extend_from_slice(&pallet_key);
		entry_key.extend_from_slice(&key_key);
		known_prefixes.push(entry_key.clone());
		if opts.omit_empty && !client.contains_data_for(&entry_key)? {
			continue;
		}
		let default = match entry.modifier {
			StorageEntryModifier::Optional => None,
			StorageEntryModifier::Default => Some(entry.default),
		};
		keyout
			.field(entry.name.clone())
			.try_value(Hex::into_untyped(Hex(entry_key.clone()))?)?;
		match entry.ty {
			StorageEntryType::Plain(v) => {
				encode_keyout.try_method(
					entry.name.clone(),
					builtin_encode_key {
						reg: registry.clone(),
						prefix: Rc::new(entry_key.clone()),
						key: Key(vec![]),
					},
				)?;
				encode_valueout.try_method(
					entry.name.clone(),
					builtin_encode_value {
						reg: registry.clone(),
						ty: ValueId(v),
					},
				)?;
				decode_valueout.try_method(
					entry.name.clone(),
					builtin_decode_value {
						reg: registry.clone(),
						ty: ValueId(v),
					},
				)?;

				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
				let should_have_entry = opts.include_defaults && default.is_some()
					|| client.contains_key(&entry_key)?;
				if !should_have_entry {
					continue;
				}

				out.field(entry.name.clone()).thunk(simple_thunk! {
					let entry_key: Vec<u8> = entry_key;
					let client: Client = client.clone();
					#[trace(skip)]
					let v: UntrackedSymbol<TypeId> = v;
					let default: Option<Vec<u8>> = default;
					let registry: Rc<PortableRegistry> = registry.clone();
					Thunk::<Val>::evaluated(fetch_decode_key(entry_key.as_slice(), client, registry, v, default)?)
				})?;
			}
			StorageEntryType::Map {
				hashers,
				key,
				value,
			} => {
				let keys = normalize_storage_map_keys(&registry, key, &hashers)?;
				encode_keyout.try_method(
					entry.name.clone(),
					builtin_encode_key {
						reg: registry.clone(),
						prefix: Rc::new(entry_key.clone()),
						key: Key(keys.clone()),
					},
				)?;
				encode_valueout.try_method(
					entry.name.clone(),
					builtin_encode_value {
						reg: registry.clone(),
						ty: ValueId(value),
					},
				)?;
				decode_valueout.try_method(
					entry.name.clone(),
					builtin_decode_value {
						reg: registry.clone(),
						ty: ValueId(value),
					},
				)?;
				key_args
					.field(entry.name.clone())
					.try_value(Val::Num(keys.len() as f64))?;

				out.field(entry.name.clone()).thunk(simple_thunk! {
					let entry_key: Vec<u8> = entry_key;
					let client: Client = client.clone();
					#[trace(skip)]
					let value: UntrackedSymbol<TypeId> = value;
					let default: Option<Vec<u8>> = default;
					let registry: Rc<PortableRegistry> = registry.clone();
					#[trace(skip)]
					let keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)> = keys;
					let opts: ChainOpts = opts;
					Thunk::<Val>::evaluated(make_fetch_keys_storage(
						client,
						entry_key,
						registry,
						keys,
						value,
						default,
						opts,
					)?)
				})?;
			}
		}
	}
	out.field("_unknown").thunk(simple_thunk! {
		let client: Client = client.clone();
		let known_prefixes: Vec<Vec<u8>> = known_prefixes;
		let pallet_key: Vec<u8> = pallet_key.to_vec();
		// #[trace(skip)]
		// let meta: RuntimeMetadataV14 = meta;
		Thunk::<Val>::evaluated({
			Val::Obj(make_unknown_key(client, &pallet_key, &known_prefixes.iter().collect::<Vec<_>>())?)
		})
	})?;
	out.field("_key").hide().try_value(keyout.build())?;
	out.field("_encodeKey")
		.hide()
		.try_value(encode_keyout.build())?;
	out.field("_encodeValue")
		.hide()
		.try_value(encode_valueout.build())?;
	out.field("_decodeValue")
		.hide()
		.try_value(decode_valueout.build())?;
	out.field("_keyArgs").hide().try_value(key_args.build())?;
	Ok(out.build())
}

#[builtin(fields(
	meta: Rc<RuntimeMetadataV14>,
))]
fn builtin_rebuild(this: &builtin_rebuild, data: ObjValue) -> Result<BTreeMap<Hex, Hex>> {
	rebuild(data, &this.meta)
}

/// Get some value under a key in client's storage as a byte array value.
fn fetch_raw(key: Vec<u8>, client: Client) -> Result<Val> {
	let value = client.get_storage(key.as_slice())?;
	Ok(if let Some(value) = value {
		Hex::into_untyped(Hex(value))?
	} else {
		// Should never occur?
		Val::Null
	})
}
fn make_unknown_key(client: Client, prefix: &[u8], known: &[&Vec<u8>]) -> Result<ObjValue> {
	let mut out = ObjValueBuilder::new();
	let pending_out = Pending::<ObjValue>::new();
	let fetched = client.get_unknown_keys(prefix, known)?;
	for key in fetched.iter().cloned() {
		let key_str = hex::to_hex(&key[prefix.len()..]);
		let value = simple_thunk! {
			let key: Vec<u8> = key;
			let client: Client = client.clone();
			Thunk::<Val>::evaluated(fetch_raw(key, client)?)
		};
		out.field(key_str).thunk(value)?;
	}
	// TODO: key filter?
	let preload_keys = simple_thunk! {
		let pending_out: Pending<ObjValue> = pending_out.clone();
		let client: Client = client;
		let fetched: Vec<Vec<u8>> = fetched;
		Thunk::<Val>::evaluated({
			eprintln!("preloading all storage keys");
			client.preload_storage(&fetched.iter().collect::<Vec<_>>())?;
			Val::Obj(pending_out.unwrap())
		})
	};
	out.field("_preloadKeys").hide().thunk(preload_keys)?;
	let out = out.build();
	pending_out.fill(out.clone());
	Ok(out)
}

/// Possibly multi-type key, pointing to a single storage entry.
#[derive(Trace, Clone)]
struct Key(#[trace(skip)] Vec<(StorageHasher, UntrackedSymbol<TypeId>)>);

/// Encode the value [`v`] into some type, denoted in the calling object's inner registry by the number [`typ`].
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    reg: Rc<PortableRegistry>,
    prefix: Rc<Vec<u8>>,
    key: Key,
))]
fn builtin_encode_key(
	this: &builtin_encode_key,
	keyi: Vec<Val>,
	from_string: Option<bool>,
) -> Result<Hex> {
	let from_string = from_string.unwrap_or(false);
	let reg = this.reg.clone();
	let key = this.key.clone();

	ensure!(
		key.0.len() == keyi.len(),
		"wrong number of keys, expected {}, got {}",
		key.0.len(),
		keyi.len()
	);

	let mut out = this.prefix.as_slice().to_owned();

	for ((h, t), k) in key.0.iter().zip(keyi) {
		encode_single_key(&reg, h.clone(), *t, k, &mut out, from_string)?;
	}

	Ok(Hex(out))
}

fn encode_single_key(
	reg: &PortableRegistry,
	hasher: StorageHasher,
	ty: UntrackedSymbol<TypeId>,
	value: Val,
	out: &mut Vec<u8>,
	from_string: bool,
) -> Result<()> {
	if from_string {
		'fs: {
			let size = match hasher {
				StorageHasher::Blake2_128 => 128 / 8,
				StorageHasher::Blake2_256 => 256 / 8,
				StorageHasher::Twox128 => 128 / 8,
				StorageHasher::Twox256 => 256 / 8,
				_ => break 'fs,
			};

			let Some(str) = value.as_str() else {
				bail!("key from string encoding with non-concat hasher only accepts hash string");
			};

			ensure!(
				str.len() == size * 2 + 2 && str.starts_with("0x"),
				"key from string encoding with non-concat hasher only accepts hash string"
			);
			let hex = hex::from_hex(&str)?;
			out.extend_from_slice(&hex);
			return Ok(());
		}
	}

	let mut encoded_key = vec![];
	encode_value(reg, ty, false, value, &mut encoded_key, from_string)?;
	let (hash, concat) = match hasher {
		StorageHasher::Blake2_128 => (blake2_128(&encoded_key).to_vec(), false),
		StorageHasher::Blake2_256 => (blake2_256(&encoded_key).to_vec(), false),
		StorageHasher::Blake2_128Concat => (blake2_128(&encoded_key).to_vec(), true),
		StorageHasher::Twox128 => (twox_128(&encoded_key).to_vec(), false),
		StorageHasher::Twox256 => (twox_256(&encoded_key).to_vec(), false),
		StorageHasher::Twox64Concat => (twox_64(&encoded_key).to_vec(), true),
		StorageHasher::Identity => (vec![], true),
	};
	out.extend(&hash);
	if concat {
		out.extend(&encoded_key);
	}
	Ok(())
}

/// Traceable wrapper of an [`UntrackedSymbol`].
#[derive(Trace, Clone)]
struct ValueId(#[trace(skip)] UntrackedSymbol<TypeId>);

/// Encode the value [`v`] into some type according to the object's supplied type [`ty`].
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    reg: Rc<PortableRegistry>,
    ty: ValueId,
))]
fn builtin_encode_value(this: &builtin_encode_value, value: Val) -> Result<Hex> {
	let reg = this.reg.clone();

	let mut out = Vec::new();
	encode_value(&reg, this.ty.0, false, value, &mut out, false)?;
	Ok(Hex(out))
}

/// Decode a [`value`] according to [`ty`], the type number of the calling object's inner registry.
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    reg: Rc<PortableRegistry>,
    ty: ValueId,
))]
fn builtin_decode_value(this: &builtin_decode_value, value: Hex) -> Result<Val> {
	decode_value(&mut value.0.as_slice(), &this.reg, this.ty.0, false).map(Val::from)
}

/// Encode the value [`v`] into some type, denoted in the calling object's inner registry by the number [`typ`].
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    reg: Rc<PortableRegistry>,
))]
fn builtin_encode(this: &builtin_encode, typ: u32, v: Val) -> Result<Hex> {
	let typ = Compact(typ).encode();
	let sym = <UntrackedSymbol<TypeId>>::decode(&mut typ.as_slice()).expect("just encoded u32");
	let mut out = Vec::new();
	encode_value(&this.reg, sym, false, v, &mut out, false)?;

	Ok(Hex(out))
}

/// Decode the value [`v`] according to [`typ`], the type number of the calling object's inner registry.
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    reg: Rc<PortableRegistry>,
))]
fn builtin_decode(this: &builtin_decode, typ: u32, v: Hex) -> Result<Val> {
	let typ = Compact(typ).encode();
	let sym = <UntrackedSymbol<TypeId>>::decode(&mut typ.as_slice()).expect("just encoded u32");

	decode_value(&mut v.0.as_slice(), &this.reg, sym, false).map(Val::from)
}

#[derive(Typed)]
struct ExtrinsicData {
	signature: Option<Signature>,
	call: Val,
}
#[derive(Typed)]
struct Signature {
	address: Val,
	signature: Val,
	extra: BTreeMap<String, Val>,
}

struct ExtrinsicEncoding {
	version: u8,
	address: UntrackedSymbol<TypeId>,
	address_type: AddressType,
	call: UntrackedSymbol<TypeId>,
	signature: UntrackedSymbol<TypeId>,
	signature_type: SignatureType,
	// extra: UntrackedSymbol<TypeId>,
	extra: Vec<(String, UntrackedSymbol<TypeId>, UntrackedSymbol<TypeId>)>,
}
fn guess_extrinsic_encoding(metadata: &RuntimeMetadataV14) -> Result<ExtrinsicEncoding> {
	let extrinsic_ty = metadata.extrinsic.ty;
	let extrinsic = metadata
		.types
		.resolve(extrinsic_ty.id)
		.expect("extrinsic ty");

	let mut params = extrinsic.type_params.iter();
	let Some(address) = params.next() else {
		bail!("param not found");
	};
	ensure!(address.name == "Address", "not address");
	let Some(address) = address.ty else {
		bail!("param not set");
	};

	let Some(call) = params.next() else {
		bail!("param not found");
	};
	ensure!(call.name == "Call", "not call");
	let Some(call) = call.ty else {
		bail!("param not set");
	};

	let Some(signature) = params.next() else {
		bail!("param not found");
	};
	ensure!(signature.name == "Signature", "not signature");
	let Some(signature) = signature.ty else {
		bail!("param not set");
	};

	let Some(extra) = params.next() else {
		bail!("param not found");
	};
	ensure!(extra.name == "Extra", "not extra");
	let Some(extra) = extra.ty else {
		bail!("param not set");
	};
	let _ = extra;

	let mut extra = vec![];
	let mut had_extra = BTreeSet::new();
	for ele in metadata.extrinsic.signed_extensions.iter() {
		extra.push((ele.identifier.clone(), ele.ty, ele.additional_signed));
		if !had_extra.insert(&ele.identifier) {
			bail!(
				"signed extension {} appeared twice, this is not supported",
				ele.identifier
			);
		};
	}

	let sigty = metadata
		.types
		.resolve(signature.id)
		.expect("missing signature");
	let signature_type = if sigty.path.segments == ["sp_runtime", "MultiSignature"] {
		SignatureType::MultiSignature
	} else {
		bail!("unknown signature type: {:?}", sigty.path);
	};

	let addrty = metadata.types.resolve(address.id).expect("missing address");
	let address_type = if addrty.path.segments == ["sp_runtime", "multiaddress", "MultiAddress"] {
		let mut params = addrty.type_params.iter();
		let Some(addr) = params.next() else {
			bail!("missing multiaddr generic");
		};
		ensure!(addr.name == "AccountId", "not param");
		let Some(addr) = addr.ty else {
			bail!("missing addr");
		};

		let inaddrty = metadata.types.resolve(addr.id).expect("missing inaddr");
		dbg!(&inaddrty.path);

		let default = if inaddrty.path.segments == ["sp_core", "crypto", "AccountId32"] {
			AddressSchema::Id32
		} else {
			bail!("unknown inaddr type: {:?}", inaddrty.path);
		};

		AddressType::MultiAddress { default }
	} else {
		bail!("unknown address type: {:?}", addrty.path);
	};

	Ok(ExtrinsicEncoding {
		version: metadata.extrinsic.version,
		address,
		address_type,
		call,
		signature,
		signature_type,
		extra,
	})
}

#[builtin(fields(
    meta: Rc<RuntimeMetadataV14>,
))]
fn builtin_decode_extrinsic(
	this: &builtin_decode_extrinsic,
	value: Hex,
	additional_signed: Option<NativeFn<((Val,), ObjValue)>>,
) -> Result<ExtrinsicData> {
	// decode_value(&mut value.0.as_slice(), &this.reg, this.ty.0, false).map(Val::from)
	let encoding = guess_extrinsic_encoding(&this.meta)?;

	let data = value.0;
	let mut cursor = data.as_slice();

	let length =
		<Compact<u32>>::decode(&mut cursor).map_err(|e| runtime_error!("bad length: {e}"))?;
	ensure!(cursor.len() == length.0 as usize, "length mismatch");

	let version = u8::decode(&mut cursor).map_err(|e| runtime_error!("bad ver: {e}"))?;

	let is_signed = version & 0b10000000 != 0;
	let version = version & 0b01111111;

	ensure!(version == encoding.version, "extrinsic version mismatch");

	let signature = if is_signed {
		let address = decode_value(&mut cursor, &this.meta.types, encoding.address, false)
			.map_err(|e| runtime_error!("bad address: {e}"))?;
		let signature = decode_value(&mut cursor, &this.meta.types, encoding.signature, false)
			.map_err(|e| runtime_error!("bad signature encoding: {e}"))?;
		let mut extra = BTreeMap::new();
		for (name, data, _) in encoding.extra.iter() {
			let data = decode_value(&mut cursor, &this.meta.types, *data, false)?;
			extra.insert(name.clone(), data);
		}
		// dbg!(&address);
		Some(Signature {
			address,
			signature,
			extra,
		})
	} else {
		None
	};
	let call = decode_value(&mut cursor, &this.meta.types, encoding.call, false)
		.map_err(|e| runtime_error!("bad call encoding: {e}"))?;
	ensure!(cursor.is_empty(), "unexpected trailing data");

	if let Some(signature) = &signature {
		let mut call_data = vec![];
		encode_value(
			&this.meta.types,
			encoding.call,
			false,
			call.clone(),
			&mut call_data,
			false,
		)?;
		let mut signing_payload = call_data;
		for (name, format, _) in encoding.extra.iter() {
			let data = signature.extra.get(name).expect("aaa");
			encode_value(
				&this.meta.types,
				*format,
				false,
				data.clone(),
				&mut signing_payload,
				false,
			)
			.with_description(|| format!("while encoding extra {name} ([] by default)"))?;
		}
		if let Some(data) = additional_signed {
			for (name, _, format) in encoding.extra.iter() {
				let data = data(BTreeMap::into_untyped(signature.extra.clone())?)?
					.get(name.into())
					.with_description(|| format!("getting data for {name}"))?
					.unwrap_or_else(|| Val::Arr(ArrValue::empty()));
				encode_value(
					&this.meta.types,
					*format,
					false,
					data,
					&mut signing_payload,
					false,
				)
				.with_description(|| {
					format!("while encoding signedextra {name} ([] by default)")
				})?;
			}
		}
		dbg!(signing_payload.len());
		if !verify_signature(
			encoding.signature_type,
			signature.signature.clone(),
			encoding.address_type,
			signature.address.clone(),
			Hex(signing_payload),
		)? {
			bail!("invalid signature");
		}
	}

	Ok(ExtrinsicData { signature, call })
}

/// Convert an address from SS58 to a hex string.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```text
/// cql.ss58("5F6kd9bskZE53HP4JZqadDvEzvrCi4179F6ma3ZV4G3U3x7Y") ==
///     "0x864481616c4bd8689a578cb28e1da470f7b819d6b6df8f4d65b50aba8f996508"
/// ```
#[builtin]
pub fn builtin_ss58(v: IStr) -> Result<Hex> {
	let s = sp_core::crypto::AccountId32::from_string(&v)
		.map_err(|e| runtime_error!("wrong ss58: {e}"))?;
	Ok(Hex(s.as_slice().into()))
}
#[builtin]
pub fn builtin_ss58_encode(raw: Hex, format: Option<Ss58Format>) -> Result<IStr> {
	let format = format.unwrap_or_default();
	let s = sp_core::crypto::AccountId32::from_slice(&raw)
		.map_err(|()| runtime_error!("bad accountid32 length"))?;
	let out = s.to_ss58check_with_version(format.0);
	Ok(out.into())
}

#[builtin]
fn builtin_description(description: IStr, value: Thunk<Val>) -> Result<Val> {
	value.evaluate().description(&description)
}

/// Create a Jsonnet object of a blockchain block.
fn make_block(client: Client, opts: ChainOpts) -> Result<ObjValue> {
	let mut out = ObjValueBuilder::new();
	let pending_out = Pending::<ObjValue>::new();
	let meta = client.get_metadata()?;
	let reg = Rc::new(meta.types.clone());
	for pallet in &meta.pallets {
		let Some(storage) = &pallet.storage else {
			continue;
		};
		if opts.omit_empty {
			let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
			if !client.contains_data_for(&pallet_key)? {
				continue;
			}
		}
		out.field(pallet.name.clone()).thunk(simple_thunk! {
			let client: Client = client.clone();
			#[trace(skip)]
			let pallet: PalletMetadata<PortableForm> = pallet.clone();
			let reg: Rc<PortableRegistry> = reg.clone();
			let opts: ChainOpts = opts;
			Thunk::<Val>::evaluated(Val::Obj(make_pallet_key(client, pallet, reg, opts)?))
		})?;
	}
	out.field("_raw").hide().thunk(simple_thunk! {
		let client: Client = client.clone();
		Thunk::<Val>::evaluated(Val::Obj(make_unknown_key(client, &[], &[])?))
	})?;
	let meta_key = metadata_obj(&meta);
	out.field("_meta").hide().try_value(meta_key)?;
	let meta = Rc::new(meta);
	out.field("_unknown").thunk(simple_thunk! {
		let client: Client = client.clone();
		#[trace(skip)]
		let meta: Rc<RuntimeMetadataV14> = meta.clone();
		Thunk::<Val>::evaluated({
			let mut known = Vec::new();
			for pallet in &meta.pallets {
				let Some(storage) = &pallet.storage else {
					continue;
				};
				let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
				known.push(pallet_key.to_vec());
			}
			Val::Obj(make_unknown_key(client, &[], &known.iter().collect::<Vec<_>>())?)
		})
	})?;
	out.method("_encode", builtin_encode { reg: reg.clone() });
	out.method("_decode", builtin_decode { reg });
	out.method(
		"_decodeExtrinsic",
		builtin_decode_extrinsic { meta: meta.clone() },
	);
	out.method("_rebuild", builtin_rebuild { meta: meta.clone() });

	let preload_keys = simple_thunk! {
		let pending_out: Pending<ObjValue> = pending_out.clone();
		let client: Client = client.clone();
		Thunk::<Val>::evaluated({
			eprintln!("preloading all keys");
			let keys = client.get_keys(&[])?;
			client.preload_storage(keys.iter().collect::<Vec<_>>().as_slice())?;
			Val::Obj(pending_out.unwrap())
		})
	};
	out.field("_preloadKeys").hide().thunk(preload_keys)?;
	let out = out.build();
	pending_out.fill(out.clone());
	Ok(out)
}

/// Create a Jsonnet object of a blockchain block.
///
/// This function is passed to Jsonnet and is callable from the code on certain objects.
#[builtin(fields(
    client: ClientShared,
    opts: ChainOpts,
))]
fn chain_block(this: &chain_block, block: u32) -> Result<ObjValue> {
	make_block(
		Client::new(
			this.client
				.block(Some(block))
				.map_err(client::Error::Live)?,
		),
		this.opts,
	)
}

/// Selection of optional flags for chain data processing.
#[derive(Typed, Trace, Default, Clone, Copy)]
pub struct ChainOpts {
	/// Whether or not to ignore trie prefixes with no keys
	pub omit_empty: bool,
	/// Should default values be included in output
	pub include_defaults: bool,
}

#[builtin]
pub fn builtin_chain(url: String, opts: Option<ChainOpts>) -> Result<ObjValue> {
	chain(url, opts, Default::default())
}

/// Get chain data from a URL, including queryable storage, metadata, and blocks.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```text
/// cql.chain("ws://localhost:9944")
/// ```
pub fn chain(url: String, opts: Option<ChainOpts>, cancel: Arc<Notify>) -> Result<ObjValue> {
	let opts = opts.unwrap_or_default();
	let client = ClientShared::new(url, cancel).map_err(client::Error::Live)?;
	let mut obj = ObjValueBuilder::new();
	obj.method(
		"block",
		chain_block {
			client: client.clone(),
			opts,
		},
	);
	obj.field("latest")
		.hide()
		.thunk(simple_thunk!{
            let client: ClientShared = client;
            let opts: ChainOpts = opts;
            Thunk::<Val>::evaluated(Val::Obj(make_block(Client::new(client.block(None).map_err(client::Error::Live)?), opts)?))
        })?;
	Ok(obj.build())
}

#[builtin]
pub fn builtin_twox128_of_string(data: IStr) -> Hex {
	Hex(twox_128(data.as_bytes()).into())
}

#[builtin]
pub fn builtin_twox128(data: Hex) -> Hex {
	Hex(twox_128(&data).into())
}

#[builtin]
pub fn builtin_keccak256(data: Hex) -> Hex {
	Hex(keccak_256(&data).into())
}

/// Create a mock block Jsonnet object from some parsed data dump.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```text
/// cql.dump(cql.chain("ws://localhost:9944").latest._meta, {
///     "a": 1,
///     "b": 2,
///     "c": 3,
/// }, {omit_empty:true})
/// ```
#[builtin]
pub fn builtin_dump(
	meta: Either![ObjValue, Hex],
	data: BTreeMap<Hex, Hex>,
	opts: Option<ChainOpts>,
) -> Result<ObjValue> {
	let opts = opts.unwrap_or_default();

	fn types_ordered(r: &PortableRegistry) -> bool {
		for (i, t) in r.types.iter().enumerate() {
			if i as u32 != t.id {
				return false;
			}
		}
		true
	}

	let mut meta: RuntimeMetadataV14 = match meta {
		Either2::A(obj) => serde_json::from_value(
			serde_json::to_value(Val::Obj(obj)).map_err(|e| runtime_error!("bad metadata: {e}"))?,
		)
		.map_err(|e| runtime_error!("bad metadata: {e}"))?,
		Either2::B(meta) => {
			match RuntimeMetadataPrefixed::decode(&mut meta.0.as_slice())
				.map_err(|e| runtime_error!("bad metadata: {e}"))?
				.1
			{
				RuntimeMetadata::V14(meta) => meta,
				_ => bail!("unknown metadata version"),
			}
		}
	};

	if !types_ordered(&meta.types) {
		meta.types.types.sort_by_key(|t| t.id);
		ensure!(
			types_ordered(&meta.types),
			"there are gaps in portable registry data"
		);
	}

	make_block(
		Client::new(ClientDump {
			meta,
			data: data.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
		}),
		opts,
	)
}

#[builtin(fields(
	cache_path: Option<PathBuf>,
))]
pub fn builtin_full_dump(
	this: &builtin_full_dump,
	data: BTreeMap<Hex, Hex>,
	opts: Option<ChainOpts>,
) -> Result<ObjValue> {
	let Some(code) = data.get(&Hex::encode_str(":code")) else {
		bail!("there is no code stored in the provided dump");
	};
	let runtime = RuntimeContainer::new(code.0.clone(), this.cache_path.as_deref());
	let meta = runtime.metadata()?;
	builtin_dump(Either2::B(Hex(meta)), data, opts)
}

#[builtin]
fn builtin_blake2_256_root(tree: BTreeMap<Hex, Hex>, state_version: u8) -> Result<Hex> {
	let state_version = match state_version {
		0 => StateVersion::V0,
		1 => StateVersion::V1,
		_ => bail!("unknown state version"),
	};
	let pairs = tree
		.into_iter()
		.map(|(k, v)| (k.0, v.0))
		.collect::<Vec<_>>();
	Ok(Hex(blake2_256_root(pairs, state_version).as_bytes().into()))
}

pub fn create_cql(wasm_cache_path: Option<PathBuf>) -> ObjValue {
	// Pass the built-in functions as macro-generated structs into the cql object available from Jsonnet code.
	let mut cql = ObjValueBuilder::new();
	cql.method("chain", builtin_chain::INST);
	cql.method("dump", builtin_dump::INST);

	cql.method("toHex", builtin_to_hex::INST);
	cql.method("fromHex", builtin_from_hex::INST);

	cql.method("ss58", builtin_ss58::INST);
	cql.method("ss58Encode", builtin_ss58_encode::INST);
	cql.method("ss58Decode", builtin_ss58::INST);
	cql.method("ethEncode", builtin_eth_encode::INST);

	cql.method("seed", builtin_seed::INST);
	cql.method("sr25519Seed", builtin_sr25519_seed::INST);
	cql.method("ed25519Seed", builtin_ed25519_seed::INST);
	cql.method("ecdsaSeed", builtin_ecdsa_seed::INST);
	cql.method("ethereumSeed", builtin_ethereum_seed::INST);

	cql.method("addressSeed", builtin_address_seed::INST);
	cql.method("sr25519AddressSeed", builtin_sr25519_address_seed::INST);
	cql.method("ed25519AddressSeed", builtin_ed25519_address_seed::INST);
	cql.method("ecdsaAddressSeed", builtin_ecdsa_address_seed::INST);
	cql.method("ethereumAddressSeed", builtin_ethereum_address_seed::INST);

	cql.method("twox128String", builtin_twox128_of_string::INST);
	cql.method("twox128", builtin_twox128::INST);
	cql.method("keccak256", builtin_keccak256::INST);

	cql.method("blake2_256Root", builtin_blake2_256_root::INST);

	cql.method(
		"fullDump",
		builtin_full_dump {
			cache_path: wasm_cache_path.clone(),
		},
	);
	cql.method(
		"runtimeWasm",
		builtin_runtime_wasm {
			cache_path: wasm_cache_path,
		},
	);

	cql.method("description", builtin_description::INST);

	cql.build()
}

#[derive(Trace)]
pub struct CqlContextInitializer {
	cql: Thunk<Val>,
}
impl Default for CqlContextInitializer {
	fn default() -> Self {
		let wasm_cache_dir = BaseDirs::new().map(|b| {
			let mut d = b.cache_dir().to_owned();
			d.push("chainql");
			d
		});
		Self {
			cql: Thunk::evaluated(Val::Obj(create_cql(wasm_cache_dir))),
		}
	}
}

impl ContextInitializer for CqlContextInitializer {
	fn reserve_vars(&self) -> usize {
		1
	}
	fn populate(
		&self,
		_for_file: jrsonnet_evaluator::parser::Source,
		_builder: &mut jrsonnet_evaluator::ContextBuilder,
	) {
		_builder.bind("cql", self.cql.clone());
	}
	fn as_any(&self) -> &dyn std::any::Any {
		self
	}
}

pub fn normalize_storage_map_keys(
	registry: &PortableRegistry,
	key: UntrackedSymbol<TypeId>,
	hashers: &[StorageHasher],
) -> Result<Vec<(StorageHasher, UntrackedSymbol<TypeId>)>> {
	let tuple = registry.resolve(key.id).expect("key tuple");
	let fields: Vec<_> = match &tuple.type_def {
		TypeDef::Composite(t) => t.fields.iter().map(|f| f.ty).collect(),
		TypeDef::Tuple(t) if hashers.len() != 1 => t.fields.to_vec(),
		_ => [key].into_iter().collect(),
	};

	let keys = if hashers.len() == 1 {
		vec![(hashers[0].clone(), key)]
	} else {
		ensure!(
			hashers.len() == fields.len(),
			"bad tuple: {:?} {:?}",
			hashers,
			tuple.type_def,
		);

		hashers
			.iter()
			.cloned()
			.zip(fields.iter().copied())
			.collect::<Vec<(_, _)>>()
	};
	Ok(keys)
}
