use std::cell::Cell;
use std::collections::BTreeMap;
use std::vec::Vec;
use std::{cell::RefCell, rc::Rc, result};

use frame_metadata::{RuntimeMetadata, RuntimeMetadataV14};
use futures::{FutureExt, StreamExt, TryStreamExt as _};
use jrsonnet_evaluator::bail;
use jrsonnet_gcmodule::Trace;
use jsonrpsee::core::ClientError;
use jsonrpsee::{proc_macros::rpc, ws_client::WsClient};
use parity_scale_codec::Decode;
use serde::Deserialize;
use thiserror::Error;
use tokio::runtime::Handle;

use super::ClientT;

#[derive(Error, Debug)]
pub enum Error {
	#[error("rpc error: {0}")]
	Rpc(#[from] ClientError),
	#[error("unsupported metadata version, only v14 is supported")]
	UnsupportedMetadataVersion,
	#[error("something is broken, keys paged chunk size has reached zero")]
	UnableToFetchAnyKey,
	#[error("block not found: {}", .0.map(|v| v.to_string()).unwrap_or_else(|| "latest".to_string()))]
	BlockNotFound(Option<u32>),
	#[error("block history is not supported")]
	BlockHistoryNotSupported,
	#[error("url: {0}")]
	UrlParse(#[from] http::uri::InvalidUri),
}
type Result<T, E = Error> = result::Result<T, E>;

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

	#[method(name = "chain_getBlockHash")]
	fn get_block_hash(&self, num: Option<u32>) -> RpcResult<Option<String>>;
}

#[derive(Clone, Trace)]
pub struct ClientShared {
	#[trace(skip)]
	real: Rc<WsClient>,
}

impl ClientShared {
	pub fn new(url: impl AsRef<str>) -> Result<Self> {
		let handle = Handle::current();
		let uri: hyper::Uri = url.as_ref().parse()?;
		let mut uri = uri.into_parts();
		let ws_scheme = http::uri::Scheme::try_from("ws").expect("valid");
		let wss_scheme = http::uri::Scheme::try_from("wss").expect("valid");
		if uri.scheme == Some(ws_scheme.clone()) || uri.scheme == Some(wss_scheme) {
			if let Some(authority) = &mut uri.authority {
				if authority.port().is_none() {
					*authority = http::uri::Authority::try_from(format!(
						"{authority}:{}",
						if uri.scheme == Some(ws_scheme) {
							9944
						} else {
							443
						}
					))
					.expect("valid");
				}
			};
		}
		let uri = hyper::Uri::from_parts(uri).expect("valid reconstruction");
		let client = handle.block_on(
			jsonrpsee::ws_client::WsClientBuilder::default()
				.max_request_size(20 * 1024 * 1024)
				.max_response_size(1024 * 1024 * 1024)
				.build(uri.to_string()),
		)?;
		Ok(Self {
			real: Rc::new(client),
		})
	}
	pub fn block(&self, num: Option<u32>) -> Result<LiveClient> {
		let handle = Handle::current();
		let block = handle
			.block_on(self.real.get_block_hash(num))?
			.ok_or(Error::BlockNotFound(num))?;

		Ok(LiveClient {
			real: self.real.clone(),
			key_value_cache: Rc::new(RefCell::new(BTreeMap::new())),
			fetched_prefixes: Rc::new(RefCell::new(Vec::new())),
			block: Rc::new(block),

			learned_max_chunk_size: Cell::new(8000),
		})
	}
}

peg::parser!(
	grammar text_error() for str {
		rule num() -> usize
			= v:$(['0'..='9']+) {? v.parse().map_err(|_| "invalid number")};

		pub rule count_exceeds_max() -> usize
			= "count exceeds maximum value. value: " num() ", max: " v:num() {v}
	}
);

#[derive(Clone, Trace)]
pub struct LiveClient {
	#[trace(skip)]
	real: Rc<WsClient>,
	#[trace(skip)]
	#[allow(clippy::type_complexity)]
	key_value_cache: Rc<RefCell<BTreeMap<Vec<u8>, Option<Vec<u8>>>>>,
	fetched_prefixes: Rc<RefCell<Vec<Vec<u8>>>>,
	#[trace(skip)]
	block: Rc<String>,

	learned_max_chunk_size: Cell<usize>,
}

#[derive(Default)]
pub struct Key(Vec<u8>);

impl LiveClient {
	pub fn get_keys(&self, prefix: &[u8]) -> Result<Vec<Key>> {
		let handle = Handle::current();
		if prefix.is_empty() {
			let prefixes: Vec<u8> = (0u8..=255).collect();
			let mut futures = vec![];
			for p in &prefixes {
				futures.push(self.get_keys_naive(std::slice::from_ref(p)));
			}
			handle.block_on(
				futures::stream::iter(futures)
					.buffer_unordered(16)
					.try_concat(),
			)
		} else {
			handle.block_on(self.get_keys_naive(prefix))
		}
	}
	pub async fn get_keys_naive(&self, prefix: &[u8]) -> Result<Vec<Key>> {
		let prefix_str = format!("0x{}", hex::encode(prefix));

		if self
			.fetched_prefixes
			.borrow()
			.iter()
			.any(|v| prefix.starts_with(v))
		{
			return Ok(self
				.key_value_cache
				.borrow()
				.keys()
				.filter(|k| k.starts_with(prefix))
				.map(|k| Key(k.to_vec()))
				.collect());
		}
		eprintln!("loading keys by prefix {prefix_str}");

		// let handle = Handle::current();
		let mut fetched = vec![];

		loop {
			let chunk_result = self
				.real
				.get_keys_paged(
					prefix_str.clone(),
					self.learned_max_chunk_size.get(),
					fetched.last().cloned(),
					Some(self.block.as_str().to_owned()),
				)
				.await;
			let chunk = match chunk_result {
				Ok(v) => v,
				Err(ClientError::Call(c)) if c.code() == 4002 => {
					if let Ok(v) = text_error::count_exceeds_max(c.message()) {
						eprintln!("server didn't like our paged keys limit, resetting to {v}");
						self.learned_max_chunk_size.set(v);
					} else {
						eprintln!("server didn't like our paged keys limit, and we can't extract its limit from {:?}, reducing in half", c.message());
						self.learned_max_chunk_size
							.set(self.learned_max_chunk_size.get() / 2);
						if self.learned_max_chunk_size.get() == 0 {
							bail!(Error::UnableToFetchAnyKey);
						}
					}
					continue;
				}
				Err(e) => return Err(e.into()),
			};

			let has_more = chunk.len() == self.learned_max_chunk_size.get();
			let len = chunk.len();
			if len != 0 {
				eprintln!("loaded {len} keys for pref {}", prefix_str);
			}
			fetched.extend(chunk);
			if !has_more {
				if !fetched.is_empty() {
					eprintln!("loaded keys, last chunk was {len}");
				}
				break;
			}
		}

		self.fetched_prefixes.borrow_mut().push(prefix.to_vec());

		let fetched = fetched
			.iter()
			.map(|k| {
				assert!(k.starts_with("0x"));
				Key(hex::decode(&k[2..]).expect("hex"))
			})
			.collect::<Vec<Key>>();
		Ok(fetched)
	}
	pub fn get_storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
		let mut cache = self.key_value_cache.borrow_mut();
		if cache.contains_key(key) {
			return Ok(cache.get(key).expect("cached").clone());
		}
		let key_str = format!("0x{}", hex::encode(key));
		eprintln!("loading key {key_str}");

		let handle = Handle::current();
		let value = handle.block_on(
			self.real
				.get_storage(key_str, Some(self.block.as_str().to_owned())),
		)?;
		let value = if let Some(value) = value {
			assert!(value.starts_with("0x"));
			let value = &value[2..];
			let data = hex::decode(value).expect("hex value");
			Some(data)
		} else {
			None
		};
		cache.insert(key.to_vec(), value.clone());
		Ok(value)
	}
	pub fn preload_storage(&self, keys: &[&Vec<u8>]) -> Result<()> {
		let handle = Handle::current();
		handle.block_on(
			futures::stream::iter(
				keys.chunks(60000)
					.map(|slice| self.preload_storage_fallback(slice)),
			)
			.buffer_unordered(16)
			.try_collect::<()>(),
		)?;
		// for chunk in  {
		// 	self.preload_storage_fallback(chunk)?;
		// }
		Ok(())
	}
	async fn preload_storage_fallback(&self, keys: &[&Vec<u8>]) -> Result<()> {
		let chunk_size = keys.len();
		match self.preload_storage_naive(keys).await {
			Ok(()) => Ok(()),
			Err(Error::Rpc(ClientError::Call(c))) if c.code() == -32702 || c.code() == -32008 => {
				let (keysa, keysb) = keys.split_at(chunk_size / 2);
				self.preload_storage_fallback(keysa).boxed_local().await?;
				self.preload_storage_fallback(keysb).boxed_local().await?;
				Ok(())
			}
			Err(e) => Err(e),
		}
	}
	async fn preload_storage_naive(&self, keys: &[&Vec<u8>]) -> Result<()> {
		let mut list = Vec::new();
		{
			let cache = self.key_value_cache.borrow_mut();
			for key in keys {
				if cache.contains_key(key.as_slice()) {
					continue;
				}
				let key_str = format!("0x{}", hex::encode(key));
				list.push(key_str);
			}
			drop(cache);
		}
		eprintln!("preloading {} keys", list.len());
		// let handle = Handle::current();
		let value = self
			.real
			.query_storage(list, Some(self.block.as_str().to_owned()))
			.await?;
		if value.is_empty() {
			return Ok(());
		}
		assert!(value.len() == 1);
		let value = &value[0].changes;
		let mut cache = self.key_value_cache.borrow_mut();
		for (key, value) in value {
			assert!(key.starts_with("0x"));
			let key = &key[2..];
			let key = hex::decode(key).expect("hex value");
			if let Some(value) = value {
				assert!(value.starts_with("0x"));
				let value = &value[2..];
				let data = hex::decode(value).expect("hex value");
				cache.insert(key, Some(data));
			} else {
				cache.insert(key, None);
			}
		}
		Ok(())
	}
	pub fn get_metadata(&self) -> Result<RuntimeMetadataV14> {
		eprintln!("loading metadata");
		let handle = Handle::current();
		let meta = handle.block_on(self.real.get_metadata(Some(self.block.as_str().to_owned())))?;
		assert!(meta.starts_with("0x"));
		let meta = hex::decode(&meta[2..]).expect("decode hex");
		assert!(&meta[0..4] == b"meta");
		let meta = &meta[4..];
		let meta = RuntimeMetadata::decode(&mut &meta[..]).expect("decode");
		if let RuntimeMetadata::V14(v) = meta {
			Ok(v)
		} else {
			Err(Error::UnsupportedMetadataVersion)
		}
	}
	fn contains_data_for(&self, prefix: &[u8]) -> Result<bool> {
		if self
			.fetched_prefixes
			.borrow()
			.iter()
			.any(|p| prefix.starts_with(p))
		{
			// Relevant prefix is fully fetched
			if let Some((key, _)) = self
				.key_value_cache
				.borrow()
				.range(prefix.to_owned()..)
				.next()
			{
				// We next or same key as wanted is...
				if key.starts_with(prefix) {
					// Equals/starts with
					return Ok(true);
				}
			}
			return Ok(false);
		}
		eprintln!("checking for keys under {prefix:0>2x?}");
		let prefix_str = format!("0x{}", hex::encode(prefix));

		let handle = Handle::current();
		let chunk = handle.block_on(self.real.get_keys_paged(
			prefix_str,
			1,
			None,
			Some(self.block.as_str().to_owned()),
		))?;
		Ok(!chunk.is_empty())
	}
}

impl ClientT for LiveClient {
	fn get_keys(&self, prefix: &[u8]) -> super::Result<Vec<Vec<u8>>> {
		Ok(self.get_keys(prefix)?.into_iter().map(|v| v.0).collect())
	}

	fn get_storage(&self, key: &[u8]) -> super::Result<Option<Vec<u8>>> {
		Ok(self.get_storage(key)?)
	}

	fn preload_storage(&self, keys: &[&Vec<u8>]) -> super::Result<()> {
		Ok(self.preload_storage(keys)?)
	}

	fn get_metadata(&self) -> super::Result<RuntimeMetadataV14> {
		Ok(self.get_metadata()?)
	}

	fn contains_data_for(&self, prefix: &[u8]) -> super::Result<bool> {
		Ok(self.contains_data_for(prefix)?)
	}

	fn next(&self) -> super::Result<super::Client> {
		Err(Error::BlockHistoryNotSupported.into())
	}
}
