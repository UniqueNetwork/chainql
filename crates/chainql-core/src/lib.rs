use std::{
	any::TypeId,
	collections::{BTreeMap, HashSet},
	rc::Rc,
	str::FromStr,
};

use client::{dump::ClientDump, live::ClientShared, Client, ClientT};
use frame_metadata::{
	PalletMetadata, RuntimeMetadataV14, StorageEntryModifier, StorageEntryType, StorageHasher,
};
use jrsonnet_evaluator::{
	error::{Error as JrError, ErrorKind::RuntimeError, Result},
	function::{builtin, FuncVal},
	tb, throw,
	typed::Typed,
	val::{ArrValue, StrValue, ThunkValue},
	ContextInitializer, IStr, ObjValue, ObjValueBuilder, Pending, State, Thunk, Val,
};
use jrsonnet_gcmodule::{Cc, Trace};
use num_bigint::BigInt;
use parity_scale_codec::{Compact, Decode, Encode, Input, Output};
use rebuild::rebuild;
use scale_info::{
	form::PortableForm, interner::UntrackedSymbol, Field, PortableRegistry, TypeDef,
	TypeDefPrimitive,
};
use serde::Deserialize;
use sp_core::{
	blake2_128, blake2_256,
	crypto::{Ss58AddressFormat, Ss58Codec},
	twox_128, twox_256, twox_64, ByteArray, Pair, U256,
};
use wasm::{builtin_runtime_wasm, RuntimeContainer};

mod client;
pub mod hex;
pub mod rebuild;
pub mod wasm;

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
            jrsonnet_evaluator::throw!($($tt)+)
        }
    };
}

/// Format a string and transform it into an error.
#[macro_export]
macro_rules! anyhow {
    ($($tt:tt)+) => {
        jrsonnet_evaluator::error::Error::from(jrsonnet_evaluator::error::ErrorKind::RuntimeError(format!($($tt)+).into()))
    };
}

/// Return a missing resolve error.
fn missing_resolve() -> JrError {
	anyhow!("invalid metadata: missing resolve key")
}

/// Return a codec error.
fn codec_error(err: parity_scale_codec::Error) -> JrError {
	anyhow!("codec: {}", err)
}

/// Return an error with the client.
fn client_error(err: client::Error) -> JrError {
	anyhow!("client: {}", err)
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
					.ok_or_else(|| anyhow!("missing field {field_name}"))?;
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
		out.member(
			f.name
				.clone()
				.unwrap_or_else(|| format!("unnamed{}", i))
				.into(),
		)
		.value(field)?;
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
		let value: Val =
			serde_json::from_str(&str).map_err(|e| RuntimeError(format!("json: {e}").into()))?;
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
		_ => throw!("unexpected type: {}", v.value_type()),
	};
	Ok(v.to_string()
		.parse()
		.map_err(|e| RuntimeError(format!("bigint encode: {e}").into()))?)
}
fn bigint_decode<T: std::fmt::Display>(v: T) -> Result<Val> {
	let v = v.to_string();
	let v: BigInt = v
		.parse()
		.map_err(|e| RuntimeError(format!("bigint decode: {e}").into()))?;
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
			throw!("variant not found: {name}");
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
			let v = Vec::<Val>::from_untyped(val)?;
			ensure!(
				e.fields.len() == v.len(),
				"tuple has wrong number of elements"
			);
			for (ty, val) in e.fields.iter().zip(v.iter()) {
				encode_value(reg, *ty, compact, val.clone(), out, false)?;
			}
		}
		TypeDef::Primitive(p) => match p {
			TypeDefPrimitive::Bool => {
				let val = maybe_json_parse(val, from_string)?;
				let b = bool::from_untyped(val)?;
				b.encode_to(out)
			}
			TypeDefPrimitive::Char => throw!("char not supported"),
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
				throw!("i256 not supported");
			}
		},
		TypeDef::Compact(_) => encode_value(reg, typ, true, val, out, from_string)?,
		TypeDef::BitSequence(_) => throw!("bitseq not supported"),
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
							return Ok(Val::Str(StrValue::Flat(var.name.as_str().into())));
						}
						let mut obj = ObjValueBuilder::new();
						let val = decode_obj_value(dec, reg, &var.fields, compact)?;
						obj.member(var.name.as_str().into()).value(val)?;

						return Ok(Val::Obj(obj.build()));
					}
				}
				throw!("invalid metadata: missing variant")
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
					reg.resolve(arr.type_param.id).expect("type exist").type_def,
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
				let mut out = vec![];
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
				TypeDefPrimitive::Char => throw!("char not supported"),
				TypeDefPrimitive::Str => {
					let val = String::decode(dec).map_err(codec_error)?;
					Val::Str(StrValue::Flat(val.into()))
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
					Val::Str(StrValue::Flat(val.to_string().into()))
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
					throw!("i256 not supported");
				}
			},
			TypeDef::Compact(c) => decode_value(dec, reg, c.type_param, true)?,
			TypeDef::BitSequence(_) => throw!("bitseq not supported"),
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
	let value = client.get_storage(key).map_err(client_error)?;
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
		keyout.member(value.clone()).value(Val::Str(StrValue::Flat(
			format!("0x{}", hex::encode(&prefix)).into(),
		)))?;
<<<<<<< HEAD
		if c.current_key_depth + 1 == c.shared.keys.len() {
			// Next value is not submap
			let should_have_entry = 
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
				c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_key(&prefix).map_err(client_error)?;
			if !should_have_entry {
				continue;
			}
		} else {
			// Submap
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
			let should_have_entry = c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_data_for(&prefix).map_err(client_error)?;
			if !should_have_entry {
				continue;
			}
		}
		keyout
			.member(value.clone())
			.value(Hex::into_untyped(Hex(prefix.clone()))?)?;

		if c.current_key_depth + 1 == c.shared.keys.len() {
			// Next value is not submap
			let should_have_entry = 
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
				c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_key(&prefix).map_err(client_error)?;
			if !should_have_entry {
				continue;
			}
		} else {
			// Submap
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
			let should_have_entry = c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_data_for(&prefix).map_err(client_error)?;
			if !should_have_entry {
				continue;
			}
		}
		if c.current_key_depth + 1 == c.shared.keys.len() {
			// Next value is not submap
			let should_have_entry = 
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
				c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_key(&prefix).map_err(client_error)?;
			if !should_have_entry {
				continue;
			}
		} else {
			// Submap
				// Optional values have no map entry by convention, so we skip this key even when !include_defaults
			let should_have_entry = c.shared.opts.include_defaults &&c.shared.value_default.is_some() ||
				c.shared.client.contains_data_for(&prefix).map_err(client_error)?;
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
		out.member(value.clone()).thunk(bound)?;
	}
	let preload_keys = simple_thunk! {
		let shared: Rc<SharedMapFetcherContext> = c.shared;
		let prefix: Rc<Vec<u8>> = c.prefix;
		let pending_out: Pending<ObjValue> = pending_out.clone();
		Thunk::<Val>::evaluated({
			eprintln!("preloading subset of keys by prefix: {prefix:0>2x?}");
			let prefixes = shared.fetched.iter().filter(|k| k.starts_with(&prefix)).collect::<Vec<_>>();
			shared.client.preload_storage(prefixes.as_slice()).map_err(client_error)?;
			Val::Obj(pending_out.unwrap())
		})
	};
	out.member("_preloadKeys".into())
		.hide()
		.thunk(preload_keys)?;
	out.member("_key".into())
		.hide()
		.value(Val::Obj(keyout.build()))?;
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
	let fetched = client.get_keys(prefix.as_slice()).map_err(client_error)?;
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
		if opts.omit_empty && !client.contains_data_for(&entry_key).map_err(client_error)? {
			continue;
		}
		let default = match entry.modifier {
			StorageEntryModifier::Optional => None,
			StorageEntryModifier::Default => Some(entry.default),
		};
		keyout
			.member(entry.name.clone().into())
			.value(Hex::into_untyped(Hex(entry_key.clone()))?)?;
		match entry.ty {
			StorageEntryType::Plain(v) => {
				encode_keyout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_encode_key {
							reg: registry.clone(),
							prefix: Rc::new(entry_key.clone()),
							key: Key(vec![])
						}
					)))))?;
				encode_valueout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_encode_value {
							reg: registry.clone(),
							ty: ValueId(v),
						}
					)))))?;
				decode_valueout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_decode_value {
							reg: registry.clone(),
							ty: ValueId(v),
						}
					)))))?;

				let should_have_entry = 
					// Optional values have no map entry by convention, so we skip this key even when !include_defaults
					opts.include_defaults && default.is_some() || 
					client.contains_key(&entry_key).map_err(client_error)?;
				if !should_have_entry {
					continue;
				}

				out.member(entry.name.clone().into()).thunk(simple_thunk! {
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
				encode_keyout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_encode_key {
							reg: registry.clone(),
							prefix: Rc::new(entry_key.clone()),
							key: Key(keys.clone())
						}
					)))))?;
				encode_valueout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_encode_value {
							reg: registry.clone(),
							ty: ValueId(value),
						}
					)))))?;
				decode_valueout
					.member(entry.name.clone().into())
					.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(
						builtin_decode_value {
							reg: registry.clone(),
							ty: ValueId(value),
						}
					)))))?;
				key_args
					.member(entry.name.clone().into())
					.value(Val::Num(keys.len() as f64))?;

				out.member(entry.name.clone().into()).thunk(simple_thunk! {
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
	out.member("_unknown".into()).thunk(simple_thunk! {
		let client: Client = client.clone();
		let known_prefixes: Vec<Vec<u8>> = known_prefixes;
		let pallet_key: Vec<u8> = pallet_key.to_vec();
		// #[trace(skip)]
		// let meta: RuntimeMetadataV14 = meta;
		Thunk::<Val>::evaluated({
			Val::Obj(make_unknown_key(client, &pallet_key, &known_prefixes.iter().collect::<Vec<_>>())?)
		})
	})?;
	out.member("_key".into())
		.hide()
		.value(Val::Obj(keyout.build()))?;
	out.member("_encodeKey".into())
		.hide()
		.value(Val::Obj(encode_keyout.build()))?;
	out.member("_encodeValue".into())
		.hide()
		.value(Val::Obj(encode_valueout.build()))?;
	out.member("_decodeValue".into())
		.hide()
		.value(Val::Obj(decode_valueout.build()))?;
	out.member("_keyArgs".into())
		.hide()
		.value(Val::Obj(key_args.build()))?;
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
	let value = client.get_storage(key.as_slice()).map_err(client_error)?;
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
	let fetched = client
		.get_unknown_keys(prefix, known)
		.map_err(client_error)?;
	for key in fetched.iter().cloned() {
		let key_str = hex::to_hex(&key[prefix.len()..]);
		let value = simple_thunk! {
			let key: Vec<u8> = key;
			let client: Client = client.clone();
			Thunk::<Val>::evaluated(fetch_raw(key, client)?)
		};
		out.member(key_str.into()).thunk(value)?;
	}
	// TODO: key filter?
	let preload_keys = simple_thunk! {
		let pending_out: Pending<ObjValue> = pending_out.clone();
		let client: Client = client;
		let fetched: Vec<Vec<u8>> = fetched;
		Thunk::<Val>::evaluated({
			eprintln!("preloading all storage keys");
			client.preload_storage(&fetched.iter().collect::<Vec<_>>()).map_err(client_error)?;
			Val::Obj(pending_out.unwrap())
		})
	};
	out.member("_preloadKeys".into())
		.hide()
		.thunk(preload_keys)?;
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

	for ((h, t), k) in key.0.iter().zip(keyi.into_iter()) {
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
				throw!("key from string encoding with non-concat hasher only accepts hash string");
			};

			if str.len() != size + 2 && !str.starts_with("0x") {
				throw!("key from string encoding with non-concat hasher only accepts hash string");
			}
			let hex = hex::from_hex(&str)?;
			out.extend_from_slice(&hex);
			return Ok(());
		}
	}

	let mut encoded_key = vec![];
	encode_value(&reg, ty, false, value, &mut encoded_key, from_string)?;
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

/// Convert an address from SS58 to a hex string.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```
/// cql.ss58("5F6kd9bskZE53HP4JZqadDvEzvrCi4179F6ma3ZV4G3U3x7Y") ==
///     "0x864481616c4bd8689a578cb28e1da470f7b819d6b6df8f4d65b50aba8f996508"
/// ```
#[builtin]
fn builtin_ss58(v: IStr) -> Result<Hex> {
	let s = sp_core::crypto::AccountId32::from_string(&v)
		.map_err(|e| RuntimeError(format!("wrong ss58: {e}").into()))?;
	Ok(Hex(s.as_slice().into()))
}
#[builtin]
fn builtin_ss58_encode(raw: Hex, format: Option<u16>) -> Result<IStr> {
	let s = sp_core::crypto::AccountId32::from_slice(&raw)
		.map_err(|()| RuntimeError("bad accountid32 length".into()))?;
	let out = s.to_ss58check_with_version(
		format
			.map(Ss58AddressFormat::custom)
			.unwrap_or_else(|| Ss58AddressFormat::custom(42)),
	);
	Ok(out.into())
}

#[builtin]
fn builtin_sr25519_seed(v: IStr) -> Result<Hex> {
	let s = sp_core::sr25519::Pair::from_string_with_seed(v.as_str(), None)
		.map_err(|e| RuntimeError(format!("invalid seed: {e:?}").into()))?;
	let public = s.0.public();
	Ok(Hex(public.as_slice().into()))
}
#[builtin]
fn builtin_ed25519_seed(v: IStr) -> Result<Hex> {
	let s = sp_core::ed25519::Pair::from_string_with_seed(v.as_str(), None)
		.map_err(|e| RuntimeError(format!("invalid seed: {e:?}").into()))?;
	let public = s.0.public();
	Ok(Hex(public.as_slice().into()))
}

}

/// Create a Jsonnet object of a blockchain block.
fn make_block(client: Client, opts: ChainOpts) -> Result<ObjValue> {
	let mut out = ObjValueBuilder::new();
	let pending_out = Pending::<ObjValue>::new();
	let meta = client.get_metadata().map_err(client_error)?;
	let reg = Rc::new(meta.types.clone());
	for pallet in &meta.pallets {
		let Some(storage) = &pallet.storage else {
			continue;
		};
		if opts.omit_empty {
			let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
			if !client
				.contains_data_for(&pallet_key)
				.map_err(client_error)?
			{
				continue;
			}
		}
		out.member(pallet.name.clone().into())
			.thunk(simple_thunk! {
				let client: Client = client.clone();
				#[trace(skip)]
				let pallet: PalletMetadata<PortableForm> = pallet.clone();
				let reg: Rc<PortableRegistry> = reg.clone();
				let opts: ChainOpts = opts;
				Thunk::<Val>::evaluated(Val::Obj(make_pallet_key(client, pallet, reg, opts)?))
			})?;
	}
	out.member("_raw".into()).hide().thunk(simple_thunk! {
		let client: Client = client.clone();
		Thunk::<Val>::evaluated(Val::Obj(make_unknown_key(client, &[], &[])?))
	})?;
	let meta_key = metadata_obj(&meta);
	out.member("_meta".into()).hide().value(meta_key)?;
	let meta = Rc::new(meta);
	out.member("_unknown".into()).thunk(simple_thunk! {
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
	out.member("_encode".into())
		.hide()
		.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode {
			reg: reg.clone()
		})))))?;
	out.member("_decode".into())
		.hide()
		.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_decode {
			reg
		})))))?;
	out.member("_rebuild".into())
		.hide()
		.value(Val::Func(FuncVal::builtin(builtin_rebuild {
			meta: meta.clone(),
		})))?;

	let preload_keys = simple_thunk! {
		let pending_out: Pending<ObjValue> = pending_out.clone();
		let client: Client = client.clone();
		Thunk::<Val>::evaluated({
			eprintln!("preloading all keys");
			let keys = client.get_keys(&[]).map_err(client_error)?;
			client.preload_storage(keys.iter().collect::<Vec<_>>().as_slice()).map_err(client_error)?;
			eprintln!("not loaded");
			Val::Obj(pending_out.unwrap())
		})
	};
	out.member("_preloadKeys".into())
		.hide()
		.thunk(preload_keys)?;
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
				.map_err(client::Error::Live)
				.map_err(client_error)?,
		),
		this.opts,
	)
}

/// Selection of optional flags for chain data processing.
#[derive(Typed, Trace, Default, Clone, Copy)]
struct ChainOpts {
	/// Whether or not to ignore trie prefixes with no keys
	omit_empty: bool,
	/// Should default values be included in output
	include_defaults: bool,
}

/// Get chain data from a URL, including queryable storage, metadata, and blocks.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```
/// cql.chain("ws://localhost:9944")
/// ```
#[builtin]
fn builtin_chain(url: String, opts: Option<ChainOpts>) -> Result<ObjValue> {
	let opts = opts.unwrap_or_default();
	let client = ClientShared::new(url)
		.map_err(client::Error::Live)
		.map_err(client_error)?;
	let mut obj = ObjValueBuilder::new();
	obj.member("block".into())
		.value(Val::Func(FuncVal::Builtin(Cc::new(tb!(chain_block {
			client: client.clone(),
			opts,
		})))))?;
	obj.member("latest".into())
        .thunk(simple_thunk!{
            let client: ClientShared = client;
            let opts: ChainOpts = opts;
            Thunk::<Val>::evaluated(Val::Obj(make_block(Client::new(client.block(None).map_err(client::Error::Live).map_err(client_error)?), opts)?))
        })?;
	Ok(obj.build())
}

#[builtin]
fn builtin_twox128_of_string(data: IStr) -> Result<Hex> {
	let data = sp_core::twox_128(data.as_bytes());
	Ok(Hex(data.into()))
}

/// Create a mock block Jsonnet object from some parsed data dump.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```
/// cql.dump(cql.chain("ws://localhost:9944").latest._meta, {
///     "a": 1,
///     "b": 2,
///     "c": 3,
/// }, {omit_empty:true})
/// ```
#[builtin]
fn builtin_dump(meta: Val, dump: ObjValue, opts: Option<ChainOpts>) -> Result<ObjValue> {
	let opts = opts.unwrap_or_default();
	let meta: RuntimeMetadataV14 = serde_json::from_value(
		serde_json::to_value(meta).map_err(|_| RuntimeError("bad metadata".into()))?,
	)
	.unwrap();
	let mut data = BTreeMap::new();
	for key in dump.fields(true) {
		let k = from_hex(&key)?;
		let v = dump.get(key)?.expect("iterating over fields");
		let v = v
			.as_str()
			.ok_or_else(|| RuntimeError("bad dump data".into()))?;
		let v = from_hex(&v)?;
		data.insert(k, v);
	}
	make_block(Client::new(ClientDump { meta, data }), opts)
}

/// Convert an array of bytes to a hex string.
fn to_hex(data: &[u8]) -> String {
	let mut out = vec![0; data.len() * 2 + 2];
	out[0] = b'0';
	out[1] = b'x';
	hex::encode_to_slice(data, &mut out[2..]).expect("size is correct");
	String::from_utf8(out).expect("hex is utf-8 compatible")
}

/// Convert an array of bytes to a hex string.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```
/// cql.toHex([0, 0, 0, 2, 16, 62, 200, 1]) == "0x00000002103ec801"
/// ```
#[builtin]
fn builtin_to_hex(data: Vec<u8>) -> Result<String> {
	Ok(to_hex(&data))
}

/// Convert a hex string to a vector of bytes.
fn from_hex(data: &str) -> Result<Vec<u8>> {
	ensure!(data.starts_with("0x"), "string doesn't starts with 0x");
	let out =
		hex::decode(&data.as_bytes()[2..]).map_err(|e| anyhow!("failed to decode hex: {e}"))?;
	Ok(out)
}

/// Convert a hex string to a vector of bytes.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```
/// cql.fromHex("0x00000002103ec801") == [0, 0, 0, 2, 16, 62, 200, 1]
/// ```
#[builtin]
fn builtin_from_hex(data: IStr) -> Result<Vec<u8>> {
	from_hex(&data)
}

pub fn create_cql() -> ObjValue {
	// Pass the built-in functions as macro-generated structs into the cql object available from Jsonnet code.
	let mut cql = ObjValueBuilder::new();
	cql.member("chain".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_chain::INST)));
	cql.member("dump".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_dump::INST)));

	cql.member("toHex".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_to_hex::INST)));
	cql.member("fromHex".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_from_hex::INST)));
	cql.member("ss58".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_ss58::INST)));
	cql.member("ss58Encode".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(builtin_ss58_encode::INST)));

	cql.member("sr25519Seed".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(
			builtin_sr25519_seed::INST,
		)));
	cql.member("ed25519Seed".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(
			builtin_ed25519_seed::INST,
		)));

	cql.member("twox128String".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(
			builtin_twox128_of_string::INST,
		)));


	cql.member("runtimeWasm".into())
		.hide()
		.value_unchecked(Val::Func(FuncVal::StaticBuiltin(
			builtin_runtime_wasm::INST,
		)));

	cql.build()
}

#[derive(Trace)]
pub struct CqlContextInitializer {
	cql: Thunk<Val>,
}
impl Default for CqlContextInitializer {
	fn default() -> Self {
		Self {
			cql: Thunk::evaluated(Val::Obj(create_cql())),
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
		_builder.bind("cql".into(), self.cql.clone());
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
		_ => [key.clone()].into_iter().collect(),
	};

	let keys = if hashers.len() == 1 {
		vec![(hashers[0].clone(), key.clone())]
	} else {
		ensure!(
			hashers.len() == fields.len(),
			"bad tuple: {:?} {:?}",
			hashers,
			tuple.type_def,
		);

		hashers
			.into_iter()
			.cloned()
			.zip(fields.iter().copied())
			.collect::<Vec<(_, _)>>()
	};
	Ok(keys)
}
