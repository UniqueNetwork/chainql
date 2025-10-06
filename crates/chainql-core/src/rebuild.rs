use std::{any::TypeId, collections::BTreeMap};

use frame_metadata::{
	PalletStorageMetadata, RuntimeMetadataV14, StorageEntryMetadata, StorageEntryType,
	StorageHasher,
};
use jrsonnet_evaluator::{bail, runtime_error, typed::Typed, ObjValue, Result, ResultExt, Val};
use scale_info::{form::PortableForm, interner::UntrackedSymbol, PortableRegistry};
use sp_core::twox_128;

use crate::{encode_single_key, encode_value, hex::Hex, normalize_storage_map_keys};

struct StorageBuilder {
	prefix_lens: Vec<usize>,
	current_prefix: Vec<u8>,
	out: BTreeMap<Hex, Hex>,
}
impl StorageBuilder {
	fn new(out: BTreeMap<Hex, Hex>) -> Self {
		Self {
			prefix_lens: vec![],
			current_prefix: vec![],
			out,
		}
	}
	fn push_prefix(&mut self, v: &[u8]) {
		self.prefix_lens.push(v.len());
		self.current_prefix.extend_from_slice(v);
	}
	fn pop_prefix(&mut self) {
		let len = self.prefix_lens.pop().expect("underflow");
		self.current_prefix
			.truncate(self.current_prefix.len() - len);
	}
	fn insert(&mut self, k: &[u8], v: Vec<u8>) {
		let mut key = self.current_prefix.to_vec();
		key.extend_from_slice(k);
		assert!(self.out.insert(Hex(key), Hex(v)).is_none());
	}
	fn finish(self) -> BTreeMap<Hex, Hex> {
		assert!(
			self.prefix_lens.is_empty() && self.current_prefix.is_empty(),
			"push/pop mismatch"
		);
		self.out
	}
}

pub fn rebuild(data: ObjValue, meta: &RuntimeMetadataV14) -> Result<BTreeMap<Hex, Hex>> {
	let mut out = StorageBuilder::new(BTreeMap::new());
	rebuild_inner(data, &mut out, meta)?;
	Ok(out.finish())
}

fn rebuild_inner(
	data: ObjValue,
	out: &mut StorageBuilder,
	meta: &RuntimeMetadataV14,
) -> Result<()> {
	let mut handled_prefixes = Vec::new();
	for (key, data) in data.iter(false) {
		if key.as_str() == "_unknown" {
			continue;
		}
		let Some(pallet) = meta.pallets.iter().find(|p| p.name == key.as_str()) else {
			bail!("unknown pallet: {key}");
		};
		let Some(storage) = &pallet.storage else {
			bail!("pallet has no storage, yet was passed to rebuild: {key}");
		};
		let pallet_prefix = twox_128(storage.prefix.as_bytes());

		let data = data?;
		let data = ObjValue::from_untyped(data)?;
		handled_prefixes.push(pallet_prefix);
		out.push_prefix(&pallet_prefix);
		tracing::info!("rebuilding pallet {}", storage.prefix);
		rebuild_pallet(data, out, &meta.types, storage)
			.with_description(|| format!("pallet <{key}> rebuild"))?;
		out.pop_prefix()
	}
	if let Some(unknown) = data.get("_unknown".into())? {
		let map = <BTreeMap<Hex, Hex>>::from_untyped(unknown)?;
		for (k, v) in map {
			if handled_prefixes.iter().any(|p| k.0.starts_with(p)) {
				bail!("unknown key starts with the known prefix")
			}
			out.insert(&k.0, v.0)
		}
	}
	Ok(())
}
fn rebuild_pallet(
	data: ObjValue,
	out: &mut StorageBuilder,
	reg: &PortableRegistry,
	meta: &PalletStorageMetadata<PortableForm>,
) -> Result<()> {
	let mut handled_prefixes = Vec::new();
	for (key, data) in data.iter(false) {
		if key.as_str() == "_unknown" {
			continue;
		}
		let Some(entry) = meta.entries.iter().find(|p| p.name == key.as_str()) else {
			bail!("unknown entry: {key}");
		};
		let storage_prefix = twox_128(entry.name.as_bytes());

		let data = match data {
			Ok(data) => data,
			Err(err) => {
				return Err(runtime_error!(
					"failed to rebuild storage {key}: {}",
					// remove a lot of nested "runtime error" messages
					err.to_string().replace("runtime error: ", "")
				));
			}
		};

		handled_prefixes.push(storage_prefix);
		out.push_prefix(&storage_prefix);
		rebuild_storage_entry(data, out, reg, entry)
			.with_description(|| format!("storage entry <{key}> rebuild"))?;
		out.pop_prefix()
	}
	if let Some(unknown) = data.get("_unknown".into())? {
		let map = <BTreeMap<Hex, Hex>>::from_untyped(unknown)?;
		for (k, v) in map {
			if handled_prefixes.iter().any(|p| k.0.starts_with(p)) {
				bail!("unknown key starts with the known prefix")
			}
			out.insert(&k.0, v.0)
		}
	}
	Ok(())
}
fn rebuild_storage_entry(
	data: Val,
	out: &mut StorageBuilder,
	reg: &PortableRegistry,
	meta: &StorageEntryMetadata<PortableForm>,
) -> Result<()> {
	match &meta.ty {
		StorageEntryType::Plain(value) => rebuild_storage(data, out, reg, &[], *value, 0),
		StorageEntryType::Map {
			hashers,
			key,
			value,
		} => {
			tracing::info!("rebuilding storage {}", meta.name);
			let keys = normalize_storage_map_keys(reg, *key, hashers)?;
			rebuild_storage(data, out, reg, &keys, *value, 0)
		}
	}
}
fn rebuild_storage(
	data: Val,
	out: &mut StorageBuilder,
	reg: &PortableRegistry,
	keys: &[(StorageHasher, UntrackedSymbol<TypeId>)],
	value: UntrackedSymbol<TypeId>,
	id: u32,
) -> Result<()> {
	if keys.is_empty() {
		let mut encoded = Vec::new();
		encode_value(reg, value, false, data, &mut encoded, false).description("value")?;
		out.insert(&[], encoded);
		return Ok(());
	}
	let (hasher, key_ty) = keys.first().expect("not empty");
	let data = ObjValue::from_untyped(data)?;
	for (key, data) in data.iter(false) {
		let mut encoded = Vec::new();
		encode_single_key(
			reg,
			hasher.clone(),
			*key_ty,
			Val::Str(key.into()),
			&mut encoded,
			true,
		)
		.with_description(|| format!("key part #{id}"))?;

		let data = data?;
		out.push_prefix(&encoded);
		rebuild_storage(data, out, reg, &keys[1..], value, id + 1)
			.with_description(|| format!("submap #{}", id + 1))?;
		out.pop_prefix();
	}
	Ok(())
}
