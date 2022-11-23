use std::{
    any::TypeId,
    collections::{BTreeMap, HashSet},
    io::Read,
    process,
    rc::Rc,
};

use clap::Parser;
use client::{dump::ClientDump, live::ClientShared, Client, ClientT};
use frame_metadata::{
    PalletMetadata, RuntimeMetadataV14, StorageEntryModifier, StorageEntryType, StorageHasher,
};
use jrsonnet_cli::{GeneralOpts, InputOpts};
use jrsonnet_evaluator::{
    error::{Error::RuntimeError, LocError, Result},
    function::{builtin, FuncVal},
    gc::TraceBox,
    tb,
    typed::{Any, Typed, VecVal},
    val::{ArrValue, ThunkValue},
    IStr, ManifestFormat, MaybeUnbound, ObjValue, ObjValueBuilder, Pending, State, Thunk, Unbound,
    Val,
};
use jrsonnet_gcmodule::{Cc, Trace};
use num_bigint::BigInt;
use num_traits::{FromPrimitive, One, Zero};
use parity_scale_codec::{Compact, Decode, Encode, Input, Output};
use scale_info::{
    form::PortableForm, interner::UntrackedSymbol, Field, PortableRegistry, TypeDef,
    TypeDefPrimitive,
};
use serde_json::Value;
use sp_core::{blake2_128, blake2_256, crypto::Ss58Codec, twox_128, twox_256, twox_64, U256};
use tokio::runtime::Handle;

mod client;

fn metadata_obj(s: State, meta: &RuntimeMetadataV14) -> Val {
    let ty = serde_json::to_value(meta).expect("valid value");
    serde_json::Value::into_untyped(ty, s).expect("valid json")
}

/// chainql
#[derive(Parser)]
struct Opts {
    #[clap(flatten)]
    general: GeneralOpts,
    #[clap(flatten)]
    input: InputOpts,
    #[clap(long, short = 'S')]
    string: bool,
}

macro_rules! simple_thunk {
    (
        let $state:ident = state;
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

            fn get(self: Box<Self>, $state: State) -> Result<Self::Output> {
                let Self {$($name),*} = *self;
                Ok($val)
            }
        }

        #[allow(clippy::redundant_field_names)]
        Thunk::new(tb!(InvisThunk {
            $($name: $expr,)*
        }))
    }};
}

macro_rules! bail {
    ($($tt:tt)+) => {
        return Err(anyhow!($($tt)+))
    }
}
macro_rules! ensure {
    ($cond:expr, $($tt:tt)+) => {
        if !($cond) {
            bail!($($tt)+)
        }
    };
}
macro_rules! anyhow {
    ($($tt:tt)+) => {
        LocError::from(jrsonnet_evaluator::error::Error::RuntimeError(format!($($tt)+).into()))
    };
}

fn missing_resolve() -> LocError {
    anyhow!("invalid metadata: missing resolve key")
}

fn codec_error(err: parity_scale_codec::Error) -> LocError {
    anyhow!("codec: {}", err)
}
fn client_error(err: client::Error) -> LocError {
    anyhow!("client: {}", err)
}

fn bound(thunk: Thunk<Val>) -> TraceBox<dyn Unbound<Bound = Thunk<Val>>> {
    #[derive(Trace)]
    struct Bound(Thunk<Val>);
    impl Unbound for Bound {
        type Bound = Thunk<Val>;

        fn bind(
            &self,
            _s: State,
            _sup: Option<ObjValue>,
            _this: Option<ObjValue>,
        ) -> Result<Self::Bound> {
            Ok(self.0.clone())
        }
    }
    tb!(Bound(thunk))
}

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

fn encode_obj_value<O>(
    s: State,
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
        return encode_value(s, reg, *typ[0].ty(), compact, val, out, false);
    }
    let val = ObjValue::from_untyped(val, s.clone())?;
    for (i, f) in typ.iter().enumerate() {
        let field_name: IStr = f
            .name()
            .cloned()
            .unwrap_or_else(|| format!("unnamed{}", i))
            .into();
        s.push_description(
            || format!(".{field_name}"),
            || {
                let field = val
                    .get(s.clone(), field_name.clone())?
                    .ok_or_else(|| anyhow!("missing field {field_name}"))?;
                encode_value(s.clone(), reg, *f.ty(), compact, field, out, false)?;
                Ok(())
            },
        )?;
    }
    Ok(())
}

fn decode_obj_value<I>(
    s: State,
    dec: &mut I,
    reg: &PortableRegistry,
    typ: &[Field<PortableForm>],
    compact: bool,
) -> Result<Val>
where
    I: Input,
{
    if typ.len() == 1 {
        return decode_value(s, dec, reg, *typ[0].ty(), compact);
    }
    let mut out = ObjValueBuilder::new();
    for (i, f) in typ.iter().enumerate() {
        let field = decode_value(s.clone(), dec, reg, *f.ty(), compact)?;
        out.member(
            f.name()
                .cloned()
                .unwrap_or_else(|| format!("unnamed{}", i))
                .into(),
        )
        .value(s.clone(), field)?;
    }
    Ok(Val::Obj(out.build()))
}

fn extract_newtypes(
    reg: &PortableRegistry,
    typ: UntrackedSymbol<TypeId>,
    compact: bool,
) -> Result<(bool, UntrackedSymbol<TypeId>)> {
    match reg
        .resolve(typ.id())
        .ok_or_else(missing_resolve)?
        .type_def()
    {
        TypeDef::Composite(c) if c.fields().len() == 1 => {
            extract_newtypes(reg, *c.fields()[0].ty(), compact)
        }
        TypeDef::Array(a) if a.len() == 1 => extract_newtypes(reg, *a.type_param(), compact),
        TypeDef::Tuple(d) if d.fields().len() == 1 => extract_newtypes(reg, d.fields()[0], compact),
        TypeDef::Compact(c) => extract_newtypes(reg, *c.type_param(), true),
        _ => Ok((compact, typ)),
    }
}
fn maybe_json_parse(s: State, v: Val, from_string: bool) -> Result<Val> {
    if !from_string {
        return Ok(v);
    }
    if let Some(str) = v.as_str() {
        let value: Value =
            serde_json::from_str(&str).map_err(|e| RuntimeError(format!("json: {e}").into()))?;
        Ok(Value::into_untyped(value, s)?)
    } else {
        Ok(v)
    }
}
fn encode_value<O>(
    s: State,
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
    match reg
        .resolve(typ.id())
        .ok_or_else(missing_resolve)?
        .type_def()
    {
        TypeDef::Composite(comp) => {
            let val = maybe_json_parse(s.clone(), val, from_string)?;
            encode_obj_value(s, reg, comp.fields(), compact, val, out)?;
        }
        TypeDef::Variant(e) => {
            if let Some(str) = val.as_str() {
                for variant in e.variants() {
                    if variant.name().as_str() == str.as_str() && variant.fields().is_empty() {
                        variant.index().encode_to(out);
                        return Ok(());
                    }
                }
            }
            let val = maybe_json_parse(s.clone(), val, from_string)?;
            let v = ObjValue::from_untyped(val, s.clone())?;
            let name = v.fields();
            ensure!(name.len() == 1, "not a enum");
            let name = name[0].clone();
            let value = v
                .get(s.clone(), name.clone())?
                .expect("value exists, as name is obtained from .fields()");

            for variant in e.variants() {
                if variant.name().as_str() == name.as_str() {
                    variant.index().encode_to(out);
                    return encode_obj_value(s, reg, variant.fields(), compact, value, out);
                }
            }
            bail!("variant not found: {name}");
        }
        TypeDef::Sequence(e) => {
            if matches!(
                reg.resolve(e.type_param().id())
                    .ok_or_else(missing_resolve)?
                    .type_def(),
                TypeDef::Primitive(TypeDefPrimitive::U8)
            ) {
                let v = String::from_untyped(val, s)?;
                let raw = from_hex(&v)?;
                raw.encode_to(out);
                return Ok(());
            }
            let val = maybe_json_parse(s.clone(), val, from_string)?;
            let v = VecVal::from_untyped(val, s.clone())?.0;
            Compact(v.len() as u32).encode_to(out);
            for val in v.iter() {
                encode_value(
                    s.clone(),
                    reg,
                    *e.type_param(),
                    compact,
                    val.clone(),
                    out,
                    false,
                )?;
            }
        }
        TypeDef::Array(e) => {
            if matches!(
                reg.resolve(e.type_param().id())
                    .ok_or_else(missing_resolve)?
                    .type_def(),
                TypeDef::Primitive(TypeDefPrimitive::U8)
            ) {
                let v = String::from_untyped(val, s)?;
                let raw = from_hex(&v)?;
                ensure!(
                    e.len() as usize == raw.len(),
                    "array has wrong number for elements, expected {}, got {}",
                    e.len(),
                    raw.len()
                );
                for i in raw {
                    i.encode_to(out);
                }
                return Ok(());
            }
            let val = maybe_json_parse(s.clone(), val, from_string)?;
            let v = VecVal::from_untyped(val, s.clone())?.0;
            ensure!(
                e.len() as usize == v.len(),
                "array has wrong number of elements, expected {}, got {}",
                e.len(),
                v.len(),
            );
            for val in v.iter() {
                encode_value(
                    s.clone(),
                    reg,
                    *e.type_param(),
                    compact,
                    val.clone(),
                    out,
                    false,
                )?;
            }
        }
        TypeDef::Tuple(e) => {
            let val = maybe_json_parse(s.clone(), val, from_string)?;
            let v = VecVal::from_untyped(val, s.clone())?.0;
            ensure!(
                e.fields().len() == v.len(),
                "tuple has wrong number of elements"
            );
            for (ty, val) in e.fields().iter().zip(v.iter()) {
                encode_value(s.clone(), reg, *ty, compact, val.clone(), out, false)?;
            }
        }
        TypeDef::Primitive(p) => match p {
            TypeDefPrimitive::Bool => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                let b = bool::from_untyped(val, s)?;
                b.encode_to(out)
            }
            TypeDefPrimitive::Char => bail!("char not supported"),
            TypeDefPrimitive::Str => {
                let s = String::from_untyped(val, s)?;
                s.encode_to(out)
            }
            TypeDefPrimitive::U8 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                let v = u8::from_untyped(val, s)?;
                v.encode_to(out)
            }
            TypeDefPrimitive::U16 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                let v = u16::from_untyped(val, s)?;
                encode_maybe_compact::<u16, _>(compact, v, out)
            }
            TypeDefPrimitive::U32 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                let v = u32::from_untyped(val, s)?;
                encode_maybe_compact::<u32, _>(compact, v, out)
            }
            TypeDefPrimitive::U64 => {
                let vs = String::from_untyped(val, s)?;
                let v: u64 = vs.parse().map_err(|e| anyhow!("{e}"))?;
                encode_maybe_compact::<u64, _>(compact, v, out)
            }
            TypeDefPrimitive::U128 => {
                let vs = String::from_untyped(val, s)?;
                let v: u128 = vs.parse().map_err(|e| anyhow!("{e}"))?;
                encode_maybe_compact::<u128, _>(compact, v, out)
            }
            TypeDefPrimitive::U256 => {
                ensure!(!compact, "U256 can't be compact");
                let vs = String::from_untyped(val, s)?;
                let v: U256 = vs.parse().map_err(|e| anyhow!("{e}"))?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I8 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                let v = i8::from_untyped(val, s)?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I16 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                ensure!(!compact, "int can't be compact");
                let v = i16::from_untyped(val, s)?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I32 => {
                let val = maybe_json_parse(s.clone(), val, from_string)?;
                ensure!(!compact, "int can't be compact");
                let v = i32::from_untyped(val, s)?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I64 => {
                ensure!(!compact, "int can't be compact");
                let vs = String::from_untyped(val, s)?;
                let v: i64 = vs.parse().map_err(|e| anyhow!("{e}"))?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I128 => {
                ensure!(!compact, "int can't be compact");
                let vs = String::from_untyped(val, s)?;
                let v: i128 = vs.parse().map_err(|e| anyhow!("{e}"))?;
                v.encode_to(out)
            }
            TypeDefPrimitive::I256 => {
                bail!("i256 not supported");
            }
        },
        TypeDef::Compact(_) => encode_value(s, reg, typ, true, val, out, from_string)?,
        TypeDef::BitSequence(_) => bail!("bitseq not supported"),
    }
    Ok(())
}
fn decode_value<I>(
    s: State,
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
        match reg
            .resolve(typ.id())
            .ok_or_else(missing_resolve)?
            .type_def()
        {
            TypeDef::Composite(c) => decode_obj_value(s, dec, reg, c.fields(), compact)?,
            TypeDef::Variant(e) => {
                let idx = u8::decode(dec).map_err(codec_error)?;
                for var in e.variants() {
                    if var.index() == idx {
                        if var.fields().is_empty() {
                            return Ok(Val::Str(var.name().as_str().into()));
                        }
                        let mut obj = ObjValueBuilder::new();
                        let val = decode_obj_value(s.clone(), dec, reg, var.fields(), compact)?;
                        obj.member(var.name().as_str().into()).value(s, val)?;

                        return Ok(Val::Obj(obj.build()));
                    }
                }
                bail!("invalid metadata: missing variant")
            }
            TypeDef::Sequence(seq) => {
                if matches!(
                    reg.resolve(seq.type_param().id())
                        .ok_or_else(missing_resolve)?
                        .type_def(),
                    TypeDef::Primitive(TypeDefPrimitive::U8)
                ) {
                    let raw = <Vec<u8>>::decode(dec).map_err(codec_error)?;
                    let mut out = vec![0; raw.len() * 2 + 2];
                    out[0] = b'0';
                    out[1] = b'x';
                    hex::encode_to_slice(&raw, &mut out[2..]).expect("size is enough");
                    return Ok(Val::Str(
                        String::from_utf8(out).expect("correct utf8").into(),
                    ));
                }

                let mut out = vec![];
                let size = <Compact<u32>>::decode(dec).map_err(codec_error)?;
                for _ in 0..size.0 {
                    let val = decode_value(s.clone(), dec, reg, *seq.type_param(), compact)?;
                    out.push(val);
                }
                Val::Arr(ArrValue::Eager(Cc::new(out)))
            }
            TypeDef::Array(arr) => {
                if matches!(
                    reg.resolve(arr.type_param().id())
                        .expect("type exist")
                        .type_def(),
                    TypeDef::Primitive(TypeDefPrimitive::U8)
                ) {
                    let mut raw = vec![0; arr.len() as usize];
                    for v in raw.iter_mut() {
                        *v = u8::decode(dec).expect("byte");
                    }
                    let mut out = vec![0; raw.len() * 2 + 2];
                    out[0] = b'0';
                    out[1] = b'x';
                    hex::encode_to_slice(&raw, &mut out[2..]).expect("size is enough");
                    return Ok(Val::Str(String::from_utf8(out).expect("utf8").into()));
                }

                let mut out = vec![];
                for _ in 0..arr.len() {
                    let val = decode_value(s.clone(), dec, reg, *arr.type_param(), compact)?;
                    out.push(val);
                }
                Val::Arr(ArrValue::Eager(Cc::new(out)))
            }
            TypeDef::Tuple(t) => {
                let mut out = vec![];
                for t in t.fields() {
                    let val = decode_value(s.clone(), dec, reg, *t, compact)?;
                    out.push(val);
                }
                Val::Arr(ArrValue::Eager(Cc::new(out)))
            }
            TypeDef::Primitive(p) => match p {
                TypeDefPrimitive::Bool => {
                    let val = bool::decode(dec).map_err(codec_error)?;
                    Val::Bool(val)
                }
                TypeDefPrimitive::Char => bail!("char not supported"),
                TypeDefPrimitive::Str => {
                    let val = String::decode(dec).map_err(codec_error)?;
                    Val::Str(val.into())
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
                    Val::Str(val.to_string().into())
                }
                TypeDefPrimitive::U128 => {
                    let val = decode_maybe_compact::<_, u128>(dec, compact)?;
                    Val::Str(val.to_string().into())
                }
                TypeDefPrimitive::U256 => {
                    ensure!(!compact, "u256 can't be compact");
                    let val = U256::decode(dec).map_err(codec_error)?;
                    Val::Str(val.to_string().into())
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
                    Val::Str(val.to_string().into())
                }
                TypeDefPrimitive::I128 => {
                    ensure!(!compact, "int can't be compact");
                    let val = i128::decode(dec).map_err(codec_error)?;
                    Val::Str(val.to_string().into())
                }
                TypeDefPrimitive::I256 => {
                    bail!("i256 not supported");
                }
            },
            TypeDef::Compact(c) => decode_value(s, dec, reg, *c.type_param(), true)?,
            TypeDef::BitSequence(_) => bail!("bitseq not supported"),
        },
    )
}

fn fetch_decode_key(
    s: State,
    key: &[u8],
    client: Client,
    registry: Rc<PortableRegistry>,
    typ: UntrackedSymbol<TypeId>,
    default: Option<Vec<u8>>,
) -> Result<Val> {
    let value = client.get_storage(key).map_err(client_error)?;
    Ok(if let Some(value) = value {
        decode_value(s, &mut &value[..], &registry, typ, false)?
    } else if let Some(default) = default {
        decode_value(s, &mut &default[..], &registry, typ, false)?
    } else {
        Val::Null
    })
}

struct SharedMapFetcherContext {
    client: Client,
    reg: Rc<PortableRegistry>,
    fetched: Vec<Vec<u8>>,
    keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)>,
    value_typ: UntrackedSymbol<TypeId>,
    value_default: Option<Vec<u8>>,
}
#[derive(Clone)]
struct MapFetcherContext {
    shared: Rc<SharedMapFetcherContext>,
    prefix: Rc<Vec<u8>>,
    current_key_depth: usize,
}
impl MapFetcherContext {
    fn key(&self) -> Option<&(StorageHasher, UntrackedSymbol<TypeId>)> {
        self.shared.keys.get(self.current_key_depth)
    }
}

fn make_fetched_keys_storage(s: State, c: MapFetcherContext) -> Result<Val> {
    let key = if let Some(k) = c.key() {
        k
    } else {
        // TODO: bulk fetching for last key and assert!(!keys.is_empty())
        return fetch_decode_key(
            s,
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
            Val::Str(to_hex(&bytes).into())
        } else {
            decode_value(s.clone(), &mut key, &c.shared.reg, key_ty, false)?
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
            value.to_string(s.clone())?
        };
        keyout.member(value.clone()).value(
            s.clone(),
            Val::Str(format!("0x{}", hex::encode(&prefix)).into()),
        )?;
        let c = MapFetcherContext {
            shared: c.shared.clone(),
            prefix: Rc::new(prefix),
            current_key_depth: c.current_key_depth + 1,
        };
        let bound = bound(simple_thunk! {
            let s = state;
            #[trace(skip)]
            let c: MapFetcherContext = c;
            Thunk::<Val>::evaluated(make_fetched_keys_storage(s, c)?)
        });
        out.member(value.clone()).bindable(s.clone(), bound)?;
    }
    let preload_keys = bound(simple_thunk! {
        let _s = state;
        let shared: Rc<SharedMapFetcherContext> = c.shared;
        let prefix: Rc<Vec<u8>> = c.prefix;
        let pending_out: Pending<ObjValue> = pending_out.clone();
        Thunk::<Val>::evaluated({
            eprintln!("preloading subset of keys by prefix: {prefix:0>2x?}");
            let prefixes = shared.fetched.iter().filter(|k| k.starts_with(&prefix)).collect::<Vec<_>>();
            shared.client.preload_storage(prefixes.as_slice()).map_err(client_error)?;
            Val::Obj(pending_out.unwrap())
        })
    });
    out.member("_preloadKeys".into())
        .hide()
        .bindable(s.clone(), preload_keys)?;
    out.member("_key".into())
        .hide()
        .value(s, Val::Obj(keyout.build()))?;
    let out = out.build();
    pending_out.fill(out.clone());
    Ok(Val::Obj(out))
}
fn make_fetch_keys_storage(
    s: State,
    client: Client,
    prefix: Vec<u8>,
    reg: Rc<PortableRegistry>,
    keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)>,
    value_typ: UntrackedSymbol<TypeId>,
    value_default: Option<Vec<u8>>,
) -> Result<Val> {
    let fetched = client.get_keys(prefix.as_slice()).map_err(client_error)?;
    make_fetched_keys_storage(
        s,
        MapFetcherContext {
            shared: Rc::new(SharedMapFetcherContext {
                client,
                reg,
                fetched,
                keys,
                value_typ,
                value_default,
            }),
            prefix: Rc::new(prefix),
            current_key_depth: 0,
        },
    )
}

fn make_pallet_key(
    s: State,
    client: Client,
    data: PalletMetadata<PortableForm>,
    registry: Rc<PortableRegistry>,
    opts: ChainOpts,
) -> Result<ObjValue> {
    let mut out = ObjValueBuilder::new();
    let mut keyout = ObjValueBuilder::new();
    let mut encode_keyout = ObjValueBuilder::new();
    let mut encode_valueout = ObjValueBuilder::new();
    let mut key_args = ObjValueBuilder::new();
    if let Some(storage) = data.storage {
        let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
        for entry in storage.entries {
            let key_key = sp_core::twox_128(entry.name.as_bytes());
            let mut entry_key = vec![];
            entry_key.extend_from_slice(&pallet_key);
            entry_key.extend_from_slice(&key_key);
            if opts.omit_empty {
                if !client.contains_data_for(&entry_key).map_err(client_error)? {
                    continue;
                }
            }
            let default = match entry.modifier {
                StorageEntryModifier::Optional => None,
                StorageEntryModifier::Default => Some(entry.default),
            };
            keyout.member(entry.name.clone().into()).value(
                s.clone(),
                Val::Str(format!("0x{}", hex::encode(&entry_key)).into()),
            )?;
            match entry.ty {
                StorageEntryType::Plain(v) => {
                    encode_keyout.member(entry.name.clone().into()).value(
                        s.clone(),
                        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode_key {
                            reg: registry.clone(),
                            prefix: Rc::new(entry_key.clone()),
                            key: Key(vec![])
                        })))),
                    )?;
                    encode_valueout.member(entry.name.clone().into()).value(
                        s.clone(),
                        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode_value {
                            reg: registry.clone(),
                            ty: ValueId(v),
                        })))),
                    )?;
                    out.member(entry.name.clone().into())
                        .binding(
                            s.clone(),
                            MaybeUnbound::Bound(simple_thunk! {
                                let s = state;
                                let entry_key: Vec<u8> = entry_key;
                                let client: Client = client.clone();
                                #[trace(skip)]
                                let v: UntrackedSymbol<TypeId> = v;
                                let default: Option<Vec<u8>> = default;
                                let registry: Rc<PortableRegistry> = registry.clone();
                                Thunk::<Val>::evaluated(fetch_decode_key(s,  entry_key.as_slice(), client, registry, v, default)?)
                            }),
                        )?;
                }
                StorageEntryType::Map {
                    hashers,
                    key,
                    value,
                } => {
                    let tuple = registry.resolve(key.id()).expect("key tuple");
                    let fields: Vec<_> = match tuple.type_def() {
                        TypeDef::Composite(t) => t.fields().iter().map(|f| f.ty()).collect(),
                        TypeDef::Tuple(t) if hashers.len() != 1 => t.fields().iter().collect(),
                        _ => [&key].into_iter().collect(),
                    };

                    let keys = if hashers.len() == 1 {
                        vec![(hashers[0].clone(), key)]
                    } else {
                        ensure!(
                            hashers.len() == fields.len(),
                            "bad tuple: {:?} {:?} {}-{}",
                            hashers,
                            tuple.type_def(),
                            storage.prefix,
                            entry.name,
                        );

                        hashers
                            .into_iter()
                            .zip(fields.iter().map(|s| **s))
                            .collect::<Vec<(_, _)>>()
                    };
                    encode_keyout.member(entry.name.clone().into()).value(
                        s.clone(),
                        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode_key {
                            reg: registry.clone(),
                            prefix: Rc::new(entry_key.clone()),
                            key: Key(keys.clone())
                        })))),
                    )?;
                    encode_valueout.member(entry.name.clone().into()).value(
                        s.clone(),
                        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode_value {
                            reg: registry.clone(),
                            ty: ValueId(value),
                        })))),
                    )?;
                    key_args
                        .member(entry.name.clone().into())
                        .value(s.clone(), Val::Num(keys.len() as f64))?;

                    out.member(entry.name.clone().into()).binding(
                        s.clone(),
                        MaybeUnbound::Bound(simple_thunk! {
                            let s = state;
                            let entry_key: Vec<u8> = entry_key;
                            let client: Client = client.clone();
                            #[trace(skip)]
                            let value: UntrackedSymbol<TypeId> = value;
                            let default: Option<Vec<u8>> = default;
                            let registry: Rc<PortableRegistry> = registry.clone();
                            #[trace(skip)]
                            let keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)> = keys;
                            Thunk::<Val>::evaluated(make_fetch_keys_storage(
                                s,
                                client,
                                entry_key,
                                registry,
                                keys,
                                value,
                                default,
                            )?)
                        }),
                    )?;
                }
            }
        }
    }
    out.member("_key".into())
        .hide()
        .value(s.clone(), Val::Obj(keyout.build()))?;
    out.member("_encodeKey".into())
        .hide()
        .value(s.clone(), Val::Obj(encode_keyout.build()))?;
    out.member("_encodeValue".into())
        .hide()
        .value(s.clone(), Val::Obj(encode_valueout.build()))?;
    out.member("_keyArgs".into())
        .hide()
        .value(s, Val::Obj(key_args.build()))?;
    Ok(out.build())
}

fn fetch_raw(key: Vec<u8>, client: Client) -> Result<Val> {
    let value = client.get_storage(key.as_slice()).map_err(client_error)?;
    Ok(if let Some(value) = value {
        Val::Arr(ArrValue::Bytes(value.as_slice().into()))
    } else {
        // Should never occur?
        Val::Null
    })
}

fn make_raw_key(s: State, client: Client) -> Result<ObjValue> {
    let mut out = ObjValueBuilder::new();
    let pending_out = Pending::<ObjValue>::new();
    let fetched = client.get_keys(&[]).map_err(client_error)?;
    for key in fetched.iter().cloned() {
        let key_str = format!("0x{}", hex::encode(&key));
        let value = bound(simple_thunk! {
            let _s = state;
            let key: Vec<u8> = key;
            let client: Client = client.clone();
            Thunk::<Val>::evaluated(fetch_raw(key, client)?)
        });
        out.member(key_str.into()).bindable(s.clone(), value)?;
    }
    // TODO: key filter?
    let preload_keys = bound(simple_thunk! {
        let _s = state;
        let pending_out: Pending<ObjValue> = pending_out.clone();
        let client: Client = client;
        let fetched: Vec<Vec<u8>> = fetched;
        Thunk::<Val>::evaluated({
            eprintln!("preloading all storage keys");
            client.preload_storage(&fetched.iter().collect::<Vec<_>>()).map_err(client_error)?;
            Val::Obj(pending_out.unwrap())
        })
    });
    out.member("_preloadKeys".into())
        .hide()
        .bindable(s, preload_keys)?;
    let out = out.build();
    pending_out.fill(out.clone());
    Ok(out)
}

#[derive(Trace, Clone)]
struct Key(#[trace(skip)] Vec<(StorageHasher, UntrackedSymbol<TypeId>)>);
#[builtin(fields(
    reg: Rc<PortableRegistry>,
    prefix: Rc<Vec<u8>>,
    key: Key,
))]
fn builtin_encode_key(
    this: &builtin_encode_key,
    s: State,
    keyi: VecVal,
    from_string: Option<bool>,
) -> Result<String> {
    let from_string = from_string.unwrap_or(false);
    let reg = this.reg.clone();
    let key = this.key.clone();

    ensure!(
        key.0.len() == keyi.0.len(),
        "wrong number of keys, expected {}, got {}",
        key.0.len(),
        keyi.0.len()
    );

    let mut out = this.prefix.as_slice().to_owned();

    'key: for ((h, t), k) in key.0.iter().zip(keyi.0.iter()) {
        let mut ko = vec![];

        if from_string {
            'fs: {
                let size = match h {
                    StorageHasher::Blake2_128 => 128 / 8,
                    StorageHasher::Blake2_256 => 256 / 8,
                    StorageHasher::Twox128 => 128 / 8,
                    StorageHasher::Twox256 => 256 / 8,
                    _ => break 'fs,
                };

                let Some(str) = k.as_str() else {
                    break 'fs;
                };

                if str.len() != size + 2 && !str.starts_with("0x") {
                    break 'fs;
                }
                let hex = from_hex(&str)?;
                out.extend_from_slice(&hex);
                continue 'key;
            }
        }

        encode_value(s.clone(), &reg, *t, false, k.clone(), &mut ko, from_string)?;
        let kh = match h {
            StorageHasher::Blake2_128 => blake2_128(&ko).to_vec(),
            StorageHasher::Blake2_256 => blake2_256(&ko).to_vec(),
            StorageHasher::Blake2_128Concat => [blake2_128(&ko).to_vec(), ko].concat(),
            StorageHasher::Twox128 => twox_128(&ko).to_vec(),
            StorageHasher::Twox256 => twox_256(&ko).to_vec(),
            StorageHasher::Twox64Concat => [twox_64(&ko).to_vec(), ko].concat(),
            StorageHasher::Identity => ko,
        };
        out.extend(&kh);
    }

    Ok(to_hex(&out))
}

#[derive(Trace, Clone)]
struct ValueId(#[trace(skip)] UntrackedSymbol<TypeId>);
#[builtin(fields(
    reg: Rc<PortableRegistry>,
    ty: ValueId,
))]
fn builtin_encode_value(this: &builtin_encode_value, s: State, value: Any) -> Result<String> {
    let reg = this.reg.clone();

    let mut out = Vec::new();
    encode_value(s, &reg, this.ty.0, false, value.0, &mut out, false)?;
    Ok(to_hex(&out))
}
#[builtin(fields(
    reg: Rc<PortableRegistry>,
))]
fn builtin_encode(this: &builtin_encode, s: State, typ: u32, v: Any) -> Result<String> {
    let typ = Compact(typ).encode();
    let sym = <UntrackedSymbol<TypeId>>::decode(&mut typ.as_slice()).expect("just encoded u32");
    let mut out = Vec::new();
    encode_value(s, &this.reg, sym, false, v.0, &mut out, false)?;

    Ok(to_hex(&out))
}
#[builtin(fields(
    reg: Rc<PortableRegistry>,
))]
fn builtin_decode(this: &builtin_decode, s: State, typ: u32, v: IStr) -> Result<Any> {
    let v = from_hex(&v)?;
    let typ = Compact(typ).encode();
    let sym = <UntrackedSymbol<TypeId>>::decode(&mut typ.as_slice()).expect("just encoded u32");

    decode_value(s, &mut v.as_slice(), &this.reg, sym, false).map(Any)
}

#[builtin]
fn builtin_ss58(v: IStr) -> Result<IStr> {
    let s = sp_core::crypto::AccountId32::from_string(&v)
        .map_err(|e| RuntimeError(format!("wrong ss58: {e}").into()))?;
    Ok(to_hex(s.as_ref()).into())
}

fn make_block(s: State, client: Client, opts: ChainOpts) -> Result<ObjValue> {
    let mut obj = ObjValueBuilder::new();
    let meta = client.get_metadata().map_err(client_error)?;
    let reg = Rc::new(meta.types.clone());
    for pallet in &meta.pallets {
        if opts.omit_empty {
            let Some(storage) = &pallet.storage else {
                continue;
            };
            let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
            if !client
                .contains_data_for(&pallet_key)
                .map_err(client_error)?
            {
                continue;
            }
        }
        obj.member(pallet.name.clone().into()).binding(
            s.clone(),
            MaybeUnbound::Bound(simple_thunk! {
                let s = state;
                let client: Client = client.clone();
                #[trace(skip)]
                let pallet: PalletMetadata<PortableForm> = pallet.clone();
                let reg: Rc<PortableRegistry> = reg.clone();
                let opts: ChainOpts = opts;
                Thunk::<Val>::evaluated(Val::Obj(make_pallet_key(s, client, pallet, reg, opts)?))
            }),
        )?;
    }
    let meta = metadata_obj(s.clone(), &meta);
    obj.member("_meta".into()).hide().value(s.clone(), meta)?;
    obj.member("_raw".into()).hide().binding(
        s.clone(),
        MaybeUnbound::Bound(simple_thunk! {
            let s = state;
            let client: Client = client;
            Thunk::<Val>::evaluated(Val::Obj(make_raw_key(s, client)?))
        }),
    )?;
    obj.member("_encode".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_encode {
            reg: reg.clone()
        })))),
    )?;
    obj.member("_decode".into()).hide().value(
        s,
        Val::Func(FuncVal::Builtin(Cc::new(tb!(builtin_decode { reg })))),
    )?;
    Ok(obj.build())
}

#[builtin(fields(
    client: ClientShared,
    opts: ChainOpts,
))]
fn chain_block(this: &chain_block, s: State, block: u32) -> Result<ObjValue> {
    make_block(
        s,
        Client::new(
            this.client
                .block(Some(block))
                .map_err(client::Error::Live)
                .map_err(client_error)?,
        ),
        this.opts,
    )
}

#[derive(Typed, Trace, Default, Clone, Copy)]
struct ChainOpts {
    omit_empty: bool,
}

#[builtin]
fn builtin_chain(s: State, url: String, opts: Option<ChainOpts>) -> Result<ObjValue> {
    let opts = opts.unwrap_or_default();
    let client = ClientShared::new(url)
        .map_err(client::Error::Live)
        .map_err(client_error)?;
    let mut obj = ObjValueBuilder::new();
    obj.member("block".into()).value(
        s.clone(),
        Val::Func(FuncVal::Builtin(Cc::new(tb!(chain_block {
            client: client.clone(),
            opts,
        })))),
    )?;
    obj.member("latest".into())
        .binding(s, MaybeUnbound::Bound(simple_thunk!{
            let s = state;
            let client: ClientShared = client;
            let opts: ChainOpts = opts;
            Thunk::<Val>::evaluated(Val::Obj(make_block(s, Client::new(client.block(None).map_err(client::Error::Live).map_err(client_error)?), opts)?))
        }))?;
    Ok(obj.build())
}

#[builtin]
fn builtin_dump(s: State, meta: Any, dump: ObjValue, opts: Option<ChainOpts>) -> Result<ObjValue> {
    let opts = opts.unwrap_or_default();
    let value = serde_json::Value::from_untyped(meta.0, s.clone())?;
    let meta: RuntimeMetadataV14 = serde_json::from_value(value).unwrap();
    let mut data = BTreeMap::new();
    for key in dump.fields() {
        let k = from_hex(&key)?;
        let v = dump.get(s.clone(), key)?.expect("iterating over fields");
        let v = v
            .as_str()
            .ok_or_else(|| RuntimeError("bad dump data".into()))?;
        let v = from_hex(&v)?;
        data.insert(k, v);
    }
    make_block(s, Client::new(ClientDump { meta, data }), opts)
}

fn to_hex(data: &[u8]) -> String {
    let mut out = vec![0; data.len() * 2 + 2];
    out[0] = b'0';
    out[1] = b'x';
    hex::encode_to_slice(data, &mut out[2..]).expect("size is correct");
    String::from_utf8(out).expect("hex is utf-8 compatible")
}

#[builtin]
fn builtin_to_hex(data: Vec<u8>) -> Result<String> {
    Ok(to_hex(&data))
}
fn from_hex(data: &str) -> Result<Vec<u8>> {
    ensure!(data.starts_with("0x"), "string doesn't starts with 0x");
    let out =
        hex::decode(&data.as_bytes()[2..]).map_err(|e| anyhow!("failed to decode hex: {e}"))?;
    Ok(out)
}

#[builtin]
fn builtin_from_hex(data: IStr) -> Result<Vec<u8>> {
    from_hex(&data)
}

#[builtin]
fn builtin_calc(ops: Vec<IStr>) -> Result<String> {
    use num_traits::Num;
    let mut stack = <Vec<BigInt>>::new();
    for op in ops {
        match op.as_str() {
            op @ ("-" | "+" | "*" | "**") => {
                let b = stack.pop().ok_or_else(|| anyhow!("missing rhs operand"))?;
                let a = stack.pop().ok_or_else(|| anyhow!("missing lhs operand"))?;
                let r = match op {
                    "-" => a - b,
                    "+" => a + b,
                    "*" => a * b,
                    "**" => {
                        let mut o = BigInt::from_u32(1).expect("0 is a valid bigint");
                        let mut c = b.clone();
                        while c != BigInt::zero() {
                            o *= a.clone();
                            c -= BigInt::one();
                        }
                        o
                    }
                    _ => unreachable!(),
                };
                stack.push(r);
            }
            v => {
                let n = BigInt::from_str_radix(v, 10)
                    .map_err(|e| anyhow!("failed to parse number: {e}"))?;
                stack.push(n);
            }
        }
    }
    ensure!(
        stack.len() == 1,
        "there should be exactly one stack element in the end"
    );
    Ok(stack[0].to_string())
}

fn main_jrsonnet(s: State) -> Result<String> {
    use jrsonnet_cli::ConfigureState;
    let opts = Opts::parse();

    opts.general.configure(&s)?;
    let mut cql = ObjValueBuilder::new();
    cql.member("chain".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_chain::INST)),
    )?;
    cql.member("dump".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_dump::INST)),
    )?;
    cql.member("toHex".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_to_hex::INST)),
    )?;
    cql.member("fromHex".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_from_hex::INST)),
    )?;
    cql.member("calc".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_calc::INST)),
    )?;
    cql.member("ss58".into()).hide().value(
        s.clone(),
        Val::Func(FuncVal::StaticBuiltin(builtin_ss58::INST)),
    )?;
    s.context_initializer()
        .as_any()
        .downcast_ref::<jrsonnet_stdlib::ContextInitializer>()
        .expect("std context")
        .settings_mut()
        .globals
        .insert("cql".into(), Thunk::evaluated(Val::Obj(cql.build())));

    let res = if opts.input.exec {
        s.evaluate_snippet("<exec>".to_owned(), opts.input.input)?
    } else if opts.input.input == "-" {
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .expect("read stdin");
        s.evaluate_snippet("<exec>".to_owned(), buf)?
    } else {
        let mut path = std::env::current_dir().expect("cwd");
        path.push(opts.input.input);
        s.import(path)?
    };
    let res = s.with_tla(res)?;

    Ok(if opts.string {
        let res = if let Some(str) = res.as_str() {
            str.as_str().to_owned()
        } else {
            bail!("expected string as output")
        };
        res
    } else {
        let res = res.manifest(s, &ManifestFormat::Json { padding: 3 })?;
        res.as_str().to_owned()
    })
}

fn main_sync() {
    let s = State::default();
    match main_jrsonnet(s.clone()) {
        Ok(e) => {
            println!("{e}");
            process::exit(0)
        }
        Err(e) => {
            eprintln!("{}", s.stringify_err(&e));
            process::exit(1)
        }
    }
}

#[tokio::main]
async fn main() {
    Handle::current()
        .spawn_blocking(main_sync)
        .await
        .expect("jrsonnet should not panic");
}
