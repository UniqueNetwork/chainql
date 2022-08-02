use std::{
    any::TypeId,
    cell::RefCell,
    collections::{HashMap, HashSet},
    io::{Cursor, Read},
    rc::Rc,
};

use clap::Parser;
use frame_metadata::{
    PalletMetadata, RuntimeMetadata, RuntimeMetadataV14, StorageEntryModifier, StorageEntryType,
    StorageHasher,
};
use jrsonnet_cli::{GeneralOpts, InputOpts};
use jrsonnet_evaluator::{
    error::Result,
    function::{builtin, FuncVal},
    gc::TraceBox,
    tb,
    typed::Typed,
    val::{ArrValue, ThunkValue},
    ManifestFormat, ObjValue, ObjValueBuilder, Pending, State, Thunk, Unbound, Val,
};
use jrsonnet_gcmodule::{Cc, Trace};
use jsonrpsee::{core::RpcResult, proc_macros::rpc, ws_client::WsClient};
use parity_scale_codec::{Compact, CompactAs, Decode, HasCompact, Input, IoReader};
use scale_info::{
    form::PortableForm, interner::UntrackedSymbol, Field, PortableRegistry, Type, TypeDef,
    TypeDefPrimitive,
};
use serde::Deserialize;
use sp_core::U256;
use tokio::runtime::Handle;

fn metadata_obj(s: State, meta: &RuntimeMetadataV14) -> Val {
    let ty = serde_json::to_value(meta).expect("valid value");
    serde_json::Value::into_untyped(ty, s).expect("valid json")
}

#[derive(Deserialize)]
pub struct QueryStorageResult {
    changes: Vec<(String, Option<String>)>,
}

#[rpc(client)]
pub trait SubstrateRpc {
    #[method(name = "state_getMetadata")]
    fn get_metadata(&self, at: Option<String>) -> RpcResult<String>;
    #[method(name = "state_getStorage")]
    fn get_storage(&self, key: String, at: Option<String>) -> RpcResult<Option<String>>;
    #[method(name = "state_queryStorageAt")]
    fn query_storage(
        &self,
        keys: Vec<String>,
        at: Option<String>,
    ) -> RpcResult<Vec<QueryStorageResult>>;
    #[method(name = "state_getKeys")]
    fn get_keys(&self, key: String, at: Option<String>) -> RpcResult<Vec<String>>;
    #[method(name = "state_getKeysPaged")]
    fn get_keys_paged(
        &self,
        key: String,
        count: usize,
        start_key: Option<String>,
        at: Option<String>,
    ) -> RpcResult<Vec<String>>;
}

/// chainql
#[derive(Parser)]
struct Opts {
    #[clap(flatten)]
    general: GeneralOpts,
    #[clap(flatten)]
    input: InputOpts,
}

macro_rules! simple_thunk {
    (
        let $state:ident = state;
        $(
            $(#[trace($meta:meta)])?
            let $name:ident: &$ty:ty = &$expr:expr;
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
                $(
                    let $name = &self.$name;
                )*
                Ok($val)
            }
        }

        Thunk::new(tb!(InvisThunk {
            $($name: $expr,)*
        }))
    }};
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

fn decode_maybe_compact<I, T>(dec: &mut I, compact: bool) -> T
where
    I: Input,
    T: Decode,
    Compact<T>: Decode,
{
    if compact {
        <Compact<T>>::decode(dec).map(|v| v.0)
    } else {
        T::decode(dec)
    }
    .unwrap_or_else(|_| panic!("{}", std::any::type_name::<T>()))
}

fn decode_obj_value<I>(
    s: State,
    dec: &mut I,
    reg: &PortableRegistry,
    typ: &[Field<PortableForm>],
    compact: bool,
) -> Val
where
    I: Input,
{
    if typ.len() == 1 {
        return decode_value(s, dec, reg, *typ[0].ty(), compact);
    }
    let mut out = ObjValueBuilder::new();
    for (i, f) in typ.iter().enumerate() {
        let field = decode_value(s.clone(), dec, reg, *f.ty(), compact);
        out.member(
            f.name()
                .cloned()
                .unwrap_or_else(|| format!("unnamed{}", i))
                .into(),
        )
        .value(s.clone(), field)
        .expect("there may be conflict");
    }
    Val::Obj(out.build())
}

fn extract_newtypes(
    reg: &PortableRegistry,
    typ: UntrackedSymbol<TypeId>,
    compact: bool,
) -> (bool, UntrackedSymbol<TypeId>) {
    match reg.resolve(typ.id()).expect("type exists").type_def() {
        TypeDef::Composite(c) if c.fields().len() == 1 => {
            extract_newtypes(reg, *c.fields()[0].ty(), compact)
        }
        TypeDef::Array(a) if a.len() == 1 => extract_newtypes(reg, *a.type_param(), compact),
        TypeDef::Tuple(d) if d.fields().len() == 1 => extract_newtypes(reg, d.fields()[0], compact),
        TypeDef::Compact(c) => extract_newtypes(reg, *c.type_param(), true),
        _ => (compact, typ),
    }
}

fn decode_value<I>(
    s: State,
    dec: &mut I,
    reg: &PortableRegistry,
    mut typ: UntrackedSymbol<TypeId>,
    mut compact: bool,
) -> Val
where
    I: Input,
{
    let (new_compact, new_typ) = extract_newtypes(reg, typ, compact);
    compact = new_compact;
    typ = new_typ;
    match reg.resolve(typ.id()).expect("type exists").type_def() {
        TypeDef::Composite(c) => decode_obj_value(s, dec, reg, c.fields(), compact),
        TypeDef::Variant(e) => {
            let idx = u8::decode(dec).expect("idx");
            for var in e.variants() {
                if var.index() == idx {
                    if var.fields().is_empty() {
                        return Val::Str(var.name().as_str().into());
                    }
                    let mut obj = ObjValueBuilder::new();
                    let val = decode_obj_value(s.clone(), dec, reg, var.fields(), compact);
                    obj.member(var.name().as_str().into())
                        .value(s, val)
                        .expect("no conflict");

                    return Val::Obj(obj.build());
                }
            }
            panic!("var not found")
        }
        TypeDef::Sequence(seq) => {
            if matches!(
                reg.resolve(seq.type_param().id())
                    .expect("type exist")
                    .type_def(),
                TypeDef::Primitive(TypeDefPrimitive::U8)
            ) {
                let raw = <Vec<u8>>::decode(dec).expect("u8arr");
                let mut out = vec![0; raw.len() * 2 + 2];
                out[0] = b'0';
                out[1] = b'x';
                hex::encode_to_slice(&raw, &mut out[2..]).expect("size is enough");
                return Val::Str(String::from_utf8(out).expect("utf8").into());
            } else if matches!(
                reg.resolve(seq.type_param().id())
                    .expect("type exist")
                    .type_def(),
                TypeDef::Primitive(TypeDefPrimitive::U16)
            ) {
                use std::fmt::Write;
                let raw = <Vec<u16>>::decode(dec).expect("u8arr");
                let mut out = String::new();
                out.push_str("wide");
                for c in raw {
                    write!(out, "{:0>4x}", c).expect("write buf");
                }
                return Val::Str(out.into());
            }

            let mut out = vec![];
            let size = <Compact<u32>>::decode(dec).expect("size");
            for _ in 0..size.0 {
                let val = decode_value(s.clone(), dec, reg, *seq.type_param(), compact);
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
                return Val::Str(String::from_utf8(out).expect("utf8").into());
            }

            let mut out = vec![];
            for _ in 0..arr.len() {
                let val = decode_value(s.clone(), dec, reg, *arr.type_param(), compact);
                out.push(val);
            }
            Val::Arr(ArrValue::Eager(Cc::new(out)))
        }
        TypeDef::Tuple(t) => {
            let mut out = vec![];
            for t in t.fields() {
                let val = decode_value(s.clone(), dec, reg, *t, compact);
                out.push(val);
            }
            Val::Arr(ArrValue::Eager(Cc::new(out)))
        }
        TypeDef::Primitive(p) => match p {
            TypeDefPrimitive::Bool => {
                let val = bool::decode(dec).expect("bool");
                Val::Bool(val)
            }
            TypeDefPrimitive::Char => panic!("char not supported"),
            TypeDefPrimitive::Str => {
                let val = String::decode(dec).expect("string");
                Val::Str(val.into())
            }
            TypeDefPrimitive::U8 => {
                let val = u8::decode(dec).expect("u8");
                Val::Num(val.into())
            }
            TypeDefPrimitive::U16 => {
                let val = decode_maybe_compact::<_, u16>(dec, compact);
                Val::Num(val.into())
            }
            TypeDefPrimitive::U32 => {
                let val = decode_maybe_compact::<_, u32>(dec, compact);
                Val::Num(val.into())
            }
            TypeDefPrimitive::U64 => {
                let val = decode_maybe_compact::<_, u64>(dec, compact);
                Val::Str(val.to_string().into())
            }
            TypeDefPrimitive::U128 => {
                let val = decode_maybe_compact::<_, u128>(dec, compact);
                Val::Str(val.to_string().into())
            }
            TypeDefPrimitive::U256 => {
                assert!(!compact);
                let val = U256::decode(dec).expect("u256");
                Val::Str(val.to_string().into())
            }
            TypeDefPrimitive::I8 => {
                let val = i8::decode(dec).expect("u8");
                Val::Num(val.into())
            }
            TypeDefPrimitive::I16 => {
                assert!(!compact);
                let val = i16::decode(dec).expect("u8");
                Val::Num(val.into())
            }
            TypeDefPrimitive::I32 => {
                let val = i32::decode(dec).expect("u8");
                Val::Num(val.into())
            }
            TypeDefPrimitive::I64 => {
                let val = i64::decode(dec).expect("u8");
                Val::Str(val.to_string().into())
            }
            TypeDefPrimitive::I128 => {
                let val = i128::decode(dec).expect("u8");
                Val::Str(val.to_string().into())
            }
            TypeDefPrimitive::I256 => {
                panic!("i256 not supported");
            }
        },
        TypeDef::Compact(c) => decode_value(s, dec, reg, *c.type_param(), true),
        TypeDef::BitSequence(_) => panic!("bitseq not supported"),
    }
}

fn make_key_fetcher_decoder(
    s: State,
    key: Rc<Vec<u8>>,
    client: Rc<DbClient>,
    registry: Rc<PortableRegistry>,
    typ: UntrackedSymbol<TypeId>,
    default: Option<Vec<u8>>,
) -> Thunk<Val> {
    let value = client.get_storage(key.as_slice());
    if let Some(value) = value {
        Thunk::evaluated(decode_value(s, &mut &value[..], &registry, typ, false))
    } else if let Some(default) = default {
        Thunk::evaluated(decode_value(s, &mut &default[..], &registry, typ, false))
    } else {
        Thunk::evaluated(Val::Null)
    }
}

struct SharedMapFetcherContext {
    client: Rc<DbClient>,
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

fn make_fetched_keys_storage(s: State, c: MapFetcherContext) -> Thunk<Val> {
    let key = if let Some(k) = c.key() {
        k
    } else {
        // TODO: bulk fetching for last key and assert!(!keys.is_empty())
        return make_key_fetcher_decoder(
            s,
            c.prefix.clone(),
            c.shared.client.clone(),
            c.shared.reg.clone(),
            c.shared.value_typ,
            c.shared.value_default.clone(),
        );
    };
    let hash_bytes = match key.0 {
        StorageHasher::Blake2_128Concat => 128 / 8,
        StorageHasher::Twox64Concat => 64 / 8,
        StorageHasher::Identity => 0,
        _ => panic!("only concat supported"),
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
        prefix.extend_from_slice(&key[..hash_bytes]);
        let mut key = &key[hash_bytes..];
        let orig_key = key;
        let key_plus_value_len = key.len();
        let value = decode_value(s.clone(), &mut key, &c.shared.reg, key_ty, false);
        // dbg!(&value);
        let value_len = key_plus_value_len - key.len();

        if visited_prefixes.contains(&orig_key[..value_len]) {
            continue;
        }
        visited_prefixes.insert(&orig_key[..value_len]);

        prefix.extend_from_slice(&orig_key[..value_len]);
        let value = if value.as_str().is_some() {
            value.as_str().expect("str")
        } else {
            value.to_string(s.clone()).expect("to string")
        };
        keyout
            .member(value.clone())
            .value(
                s.clone(),
                Val::Str(format!("0x{}", hex::encode(&prefix)).into()),
            )
            .expect("no conflict");
        let c = MapFetcherContext {
            shared: c.shared.clone(),
            prefix: Rc::new(prefix),
            current_key_depth: c.current_key_depth + 1,
        };
        let bound = bound(simple_thunk! {
            let s = state;
            #[trace(skip)]
            let c: &MapFetcherContext = &c;
            Thunk::<Val>::evaluated({
                make_fetched_keys_storage(
                    s.clone(),
                    c.clone(),
                ).evaluate(s)?
            })
        });
        out.member(value.clone())
            .bindable(s.clone(), bound)
            .expect("no conflict");
    }
    let preload_keys = bound(simple_thunk! {
        let _s = state;
        let shared: &Rc<SharedMapFetcherContext> = &c.shared;
        let prefix: &Rc<Vec<u8>> = &c.prefix;
        let pending_out: &Pending<ObjValue> = &pending_out.clone();
        Thunk::<Val>::evaluated({
            eprintln!("preloading subset of keys by prefix: {prefix:0>2x?}");
            let prefixes = shared.fetched.iter().filter(|k| k.starts_with(prefix)).collect::<Vec<_>>();
            shared.client.preload_storage(prefixes.as_slice());
            Val::Obj(pending_out.unwrap())
        })
    });
    out.member("_preloadKeys".into())
        .hide()
        .bindable(s.clone(), preload_keys)
        .expect("no conflict");
    out.member("_key".into())
        .hide()
        .value(s, Val::Obj(keyout.build()))
        .expect("no conflict");
    let out = out.build();
    pending_out.fill(out.clone());
    Thunk::evaluated(Val::Obj(out))
}
fn make_fetch_keys_storage(
    s: State,
    client: Rc<DbClient>,
    prefix: Vec<u8>,
    reg: Rc<PortableRegistry>,
    keys: Vec<(StorageHasher, UntrackedSymbol<TypeId>)>,
    value_typ: UntrackedSymbol<TypeId>,
    value_default: Option<Vec<u8>>,
) -> TraceBox<dyn Unbound<Bound = Thunk<Val>>> {
    match keys[0].0 {
        StorageHasher::Blake2_128
        | StorageHasher::Blake2_256
        | StorageHasher::Twox128
        | StorageHasher::Twox256 => {
            return bound(Thunk::evaluated(Val::Str(
                "key can't be decoded, TODO: function".into(),
            )))
        }
        StorageHasher::Blake2_128Concat | StorageHasher::Twox64Concat => {
            // Use fallback
        }
        StorageHasher::Identity => {
            // Use fallback, but clever implementation with fetching only first key layer is possible
        }
    }
    let fetched = client.get_keys(prefix.as_slice());
    bound(make_fetched_keys_storage(
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
    ))
}

fn make_pallet_key(
    client: Rc<DbClient>,
    data: PalletMetadata<PortableForm>,
    registry: Rc<PortableRegistry>,
) -> TraceBox<dyn Unbound<Bound = Thunk<Val>>> {
    #[derive(Trace)]
    struct PalletKey {
        #[trace(skip)]
        data: PalletMetadata<PortableForm>,
        #[trace(skip)]
        client: Rc<DbClient>,
        #[trace(skip)]
        registry: Rc<PortableRegistry>,
    }
    impl ThunkValue for PalletKey {
        type Output = Val;

        fn get(self: Box<Self>, s: State) -> Result<Self::Output> {
            let mut out = ObjValueBuilder::new();
            let mut keyout = ObjValueBuilder::new();
            if let Some(storage) = self.data.storage {
                let pallet_key = sp_core::twox_128(storage.prefix.as_bytes());
                for entry in storage.entries {
                    let key_key = sp_core::twox_128(entry.name.as_bytes());
                    let mut entry_key = vec![];
                    entry_key.extend_from_slice(&pallet_key);
                    entry_key.extend_from_slice(&key_key);
                    let default = match entry.modifier {
                        StorageEntryModifier::Optional => None,
                        StorageEntryModifier::Default => Some(entry.default),
                    };
                    keyout
                        .member(entry.name.clone().into())
                        .value(
                            s.clone(),
                            Val::Str(format!("0x{}", hex::encode(&entry_key)).into()),
                        )
                        .expect("no conflict");
                    match entry.ty {
                        StorageEntryType::Plain(v) => {
                            out.member(entry.name.clone().into())
                                .bindable(
                                    s.clone(),
                                    bound(make_key_fetcher_decoder(
                                        s.clone(),
                                        Rc::new(entry_key),
                                        self.client.clone(),
                                        self.registry.clone(),
                                        v,
                                        default,
                                    )),
                                )
                                .expect("no conflict");
                        }
                        StorageEntryType::Map {
                            hashers,
                            key,
                            value,
                        } => {
                            let tuple = self.registry.resolve(key.id()).expect("key tuple");
                            let fields: Vec<_> = match tuple.type_def() {
                                TypeDef::Composite(t) => {
                                    t.fields().iter().map(|f| f.ty()).collect()
                                }
                                TypeDef::Tuple(t) if hashers.len() != 1 => {
                                    t.fields().iter().collect()
                                }
                                _ => [&key].into_iter().collect(),
                            };
                            assert!(
                                hashers.len() == fields.len(),
                                "bad tuple: {:?} {}-{}",
                                tuple.type_def(),
                                storage.prefix,
                                entry.name,
                            );

                            let keys = hashers
                                .into_iter()
                                .zip(fields.iter().map(|s| **s))
                                .collect::<Vec<(_, _)>>();

                            out.member(entry.name.clone().into())
                                .bindable(
                                    s.clone(),
                                    make_fetch_keys_storage(
                                        s.clone(),
                                        self.client.clone(),
                                        entry_key,
                                        self.registry.clone(),
                                        keys,
                                        value,
                                        default,
                                    ),
                                )
                                .expect("no conflict");
                        }
                    }
                }
            }
            out.member("_key".into())
                .hide()
                .value(s, Val::Obj(keyout.build()))
                .expect("no conflict");
            Ok(Val::Obj(out.build()))
        }
    }
    bound(Thunk::new(tb!(PalletKey {
        data,
        client,
        registry
    })))
}

fn make_raw_fetcher(s: State, key: Vec<u8>, client: Rc<DbClient>) -> Thunk<Val> {
    let value = client.get_storage(key.as_slice());
    if let Some(value) = value {
        Thunk::evaluated(Val::Arr(ArrValue::Bytes(value.as_slice().into())))
    } else {
        // Should never occur?
        Thunk::evaluated(Val::Null)
    }
}

fn make_raw_key(s: State, client: Rc<DbClient>) -> Thunk<Val> {
    let mut out = ObjValueBuilder::new();
    let pending_out = Pending::<ObjValue>::new();
    let fetched = client.get_keys(&[]);
    for key in fetched.iter().cloned() {
        let key_str = format!("0x{}", hex::encode(&key));
        let value = bound(simple_thunk! {
            let s = state;
            let key: &Vec<u8> = &key;
            let client: &Rc<DbClient> = &client.clone();
            Thunk::<Val>::evaluated({
                make_raw_fetcher(s.clone(), key.clone(), client.clone()).evaluate(s)?
            })
        });
        out.member(key_str.into())
            .bindable(s.clone(), value)
            .expect("no conflict");
    }
    // TODO: key filter?
    let preload_keys = bound(simple_thunk! {
        let _s = state;
        let pending_out: &Pending<ObjValue> = &pending_out.clone();
        let client: &Rc<DbClient> = &client;
        let fetched: &Vec<Vec<u8>> = &fetched;
        Thunk::<Val>::evaluated({
            eprintln!("preloading all storage keys");
            client.preload_storage(&fetched.iter().collect::<Vec<_>>());
            Val::Obj(pending_out.unwrap())
        })
    });
    out.member("_preloadKeys".into())
        .hide()
        .bindable(s, preload_keys)
        .expect("no conflict");
    let out = out.build();
    pending_out.fill(out.clone());
    Thunk::evaluated(Val::Obj(out))
}

struct DbClient {
    real: WsClient,
    key_value_cache: RefCell<HashMap<Vec<u8>, Option<Vec<u8>>>>,
}
impl DbClient {
    fn get_keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
        eprintln!("loading keys by prefix {prefix:0>2x?}");
        let prefix_str = format!("0x{}", hex::encode(&prefix));

        let handle = Handle::try_current().expect("no runtime found");
        let mut fetched = vec![];

        loop {
            // Our gate limit
            const CHUNK: usize = 1000;
            let chunk = handle
                .block_on(self.real.get_keys_paged(
                    prefix_str.clone(),
                    CHUNK,
                    fetched.last().cloned(),
                    None,
                ))
                .expect("get keys");
            let has_more = chunk.len() == CHUNK;
            let len = chunk.len();
            eprintln!("loaded {len} keys");
            fetched.extend(chunk);
            if !has_more {
                eprintln!("loaded keys, last chunk was {len}");
                break;
            }
        }

        let fetched = fetched
            .iter()
            .map(|k| {
                assert!(k.starts_with("0x"));
                hex::decode(&k[2..]).expect("hex")
            })
            .collect::<Vec<Vec<u8>>>();
        fetched
    }
    fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
        let mut cache = self.key_value_cache.borrow_mut();
        if cache.contains_key(key) {
            return cache.get(key).expect("cached").clone();
        }
        eprintln!("loading key {key:0>2x?}");
        let key_str = format!("0x{}", hex::encode(key));

        let handle = Handle::try_current().expect("no runtime found");
        let value = handle
            .block_on(self.real.get_storage(key_str, None))
            .expect("get storage");
        let value = if let Some(value) = value {
            assert!(value.starts_with("0x"));
            let value = &value[2..];
            let data = hex::decode(&value).expect("hex value");
            Some(data)
        } else {
            None
        };
        cache.insert(key.to_vec(), value.clone());
        value
    }
    fn preload_storage(&self, keys: &[&Vec<u8>]) {
        // TODO: in case of large batches, check errors, and increase chunk size on demand
        for chunk in keys.chunks(10000) {
            self.preload_storage_naive(chunk)
        }
    }
    fn preload_storage_naive(&self, keys: &[&Vec<u8>]) {
        let mut cache = self.key_value_cache.borrow_mut();
        let mut list = Vec::new();
        for key in keys {
            if cache.contains_key(key.as_slice()) {
                continue;
            }
            let key_str = format!("0x{}", hex::encode(key));
            list.push(key_str);
        }
        eprintln!("preloading {} keys", list.len());
        let handle = Handle::try_current().expect("no runtime found");
        let value = handle
            .block_on(self.real.query_storage(list, None))
            .expect("get storage");
        if value.is_empty() {
            return;
        }
        assert!(value.len() == 1);
        let value = &value[0].changes;
        for (key, value) in value {
            assert!(key.starts_with("0x"));
            let key = &key[2..];
            let key = hex::decode(&key).expect("hex value");
            if let Some(value) = value {
                assert!(value.starts_with("0x"));
                let value = &value[2..];
                let data = hex::decode(&value).expect("hex value");
                cache.insert(key, Some(data));
            } else {
                cache.insert(key, None);
            }
        }
    }
    fn get_metadata(&self) -> RuntimeMetadataV14 {
        eprintln!("loading metadata");
        let handle = Handle::try_current().expect("no runtime found");
        let meta = handle.block_on(self.real.get_metadata(None)).expect("res");
        assert!(meta.starts_with("0x"));
        let meta = hex::decode(&meta[2..]).expect("decode hex");
        assert!(&meta[0..4] == b"meta");
        let meta = &meta[4..];
        let meta = RuntimeMetadata::decode(&mut &meta[..]).expect("decode");
        let meta = if let RuntimeMetadata::V14(v) = meta {
            v
        } else {
            panic!("only v14 supported");
        };
        meta
    }
}

#[builtin]
fn chain(s: State, url: String) -> Result<ObjValue> {
    let mut obj = ObjValueBuilder::new();
    let handle = Handle::try_current().expect("no runtime found");

    let client = handle
        .block_on(jsonrpsee::ws_client::WsClientBuilder::default().build(url))
        .expect("connection");
    let client = Rc::new(DbClient {
        real: client,
        key_value_cache: RefCell::new(HashMap::new()),
    });
    // TODO: block mapping, i.e (client("chain").blocks.latest.REST)
    let meta = client.get_metadata();
    let reg = Rc::new(meta.types.clone());
    for pallet in &meta.pallets {
        obj.member(pallet.name.clone().into())
            .bindable(
                s.clone(),
                make_pallet_key(client.clone(), pallet.clone(), reg.clone()),
            )
            .expect("pallet name is unique");
    }
    let meta = metadata_obj(s.clone(), &meta);
    obj.member("_meta".into())
        .hide()
        .value(s.clone(), meta)
        .expect("no conflict");
    obj.member("_raw".into())
        .hide()
        .bindable(
            s.clone(),
            bound(simple_thunk! {
                let s = state;
                let client: &Rc<DbClient> = &client;

                Thunk::<Val>::evaluated({
                    make_raw_key(s.clone(), client.clone()).evaluate(s)?
                })
            }),
        )
        .expect("no conflict");
    let latest_obj = obj.build();
    let mut obj = ObjValueBuilder::new();
    obj.member("latest".into())
        .value(s, Val::Obj(latest_obj))
        .expect("no conflict");
    Ok(obj.build())
}

#[builtin]
fn to_hex(data: Vec<u8>) -> Result<String> {
    Ok(format!("0x{}", hex::encode(data)))
}

#[tokio::main]
async fn main() {
    Handle::current()
        .spawn_blocking(|| {
            use jrsonnet_cli::ConfigureState;
            let opts = Opts::parse();

            let s = State::default();
            opts.general.configure(&s).expect("configure");
            let mut cql = ObjValueBuilder::new();
            cql.member("chain".into())
                .hide()
                .value(s.clone(), Val::Func(FuncVal::StaticBuiltin(chain::INST)))
                .expect("no conflict");
            cql.member("toHex".into())
                .hide()
                .value(s.clone(), Val::Func(FuncVal::StaticBuiltin(to_hex::INST)))
                .expect("no conflict");
            s.settings_mut()
                .globals
                .insert("cql".into(), Val::Obj(cql.build()));

            let res = if opts.input.exec {
                s.evaluate_snippet("<exec>".to_owned(), opts.input.input)
                    .expect("bad query")
            } else if opts.input.input == "-" {
                let mut buf = String::new();
                std::io::stdin()
                    .read_to_string(&mut buf)
                    .expect("read stdin");
                s.evaluate_snippet("<exec>".to_owned(), buf)
                    .expect("bad query")
            } else {
                let mut path = std::env::current_dir().expect("cwd");
                path.push(opts.input.input);
                s.import(path).expect("bad query")
            };
            let res = s.with_tla(res).expect("tla call failed");

            let res = res
                .manifest(s, &ManifestFormat::Json { padding: 3 })
                .expect("manifest failed");
            println!("{res}");
        })
        .await
        .expect("blocking task");
}
