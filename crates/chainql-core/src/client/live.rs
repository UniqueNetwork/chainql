use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::env;
use std::fmt::{Debug, Display};
use std::str::FromStr;
use std::time::Duration;
use std::vec::Vec;
use std::{rc::Rc, result};

use frame_metadata::{RuntimeMetadata, RuntimeMetadataV14};
use futures::{FutureExt, StreamExt, TryStreamExt as _};
use jrsonnet_evaluator::bail;
use jrsonnet_gcmodule::Trace;
use parity_scale_codec::Decode;
use thiserror::Error;
use tokio::runtime::Handle;
use tracing::{debug, error, info, info_span, Span};
use tracing_indicatif::span_ext::IndicatifSpanExt;
use tracing_indicatif::style::ProgressStyle;
use url::Url;

use crate::client::rpc::{RpcClient, RpcError};
use crate::client::rpc_http::HttpClient;
use crate::client::rpc_ws::WsClient;

use super::ClientT;

#[derive(Error, Debug)]
pub enum Error {
	#[error("url error: {0}")]
	UrlParse(#[from] url::ParseError),
	#[error("unsupported url scheme: {0}")]
	UnsupportedUrlScheme(String),
	#[error("rpc error: {0}")]
	Rpc(#[from] RpcError),
	#[error("unsupported metadata version, only v14 is supported")]
	UnsupportedMetadataVersion,
	#[error("something is broken, keys paged chunk size has reached zero")]
	UnableToFetchAnyKey,
	#[error("block not found: {}", .0.map(|v| v.to_string()).unwrap_or_else(|| "latest".to_string()))]
	BlockNotFound(Option<u32>),
	#[error("block history is not supported")]
	BlockHistoryNotSupported,
}

pub type Result<T, E = Error> = result::Result<T, E>;

#[derive(Clone, Trace)]
pub struct ClientShared {
	#[trace(skip)]
	rpc_client: Rc<Box<dyn RpcClient>>,
}

impl ClientShared {
	pub fn new(url: impl AsRef<str>) -> Result<Self> {
		let url: Url = url.as_ref().parse()?;
		let timeout: Duration = Duration::from_secs(300);

		let client: Box<dyn RpcClient> = match url.scheme() {
			"http" | "https" => {
				let client = HttpClient::new(url, timeout)?;
				Box::new(client)
			}
			"ws" | "wss" => {
				let handle = Handle::current();
				let client = handle.block_on(WsClient::new(url, timeout))?;
				Box::new(client)
			}
			scheme => {
				return Err(Error::UnsupportedUrlScheme(scheme.to_owned()));
			}
		};

		Ok(Self {
			rpc_client: Rc::new(client),
		})
	}

	pub fn block(&self, num: Option<u32>) -> Result<LiveClient> {
		let handle = Handle::current();

		let block = handle
			.block_on(self.rpc_client.get_block_hash(num))?
			.ok_or(Error::BlockNotFound(num))?;

		let max_workers = get_var("CHAINQL_WORKERS", 16);
		let keys_chunk_size = get_var("CHAINQL_KEYS_CHUNK_SIZE", 30_000);

		Ok(LiveClient {
			real: self.rpc_client.clone(),
			key_value_cache: Rc::new(RefCell::new(BTreeMap::new())),
			fetched_prefixes: Rc::new(RefCell::new(Vec::new())),
			block: Rc::new(block),

			max_workers,
			keys_chunk_size,

			learned_max_chunk_size: Cell::new(keys_chunk_size),
		})
	}
}

fn get_var<T>(var: &str, default: T) -> T
where
	T: FromStr,
	T::Err: Display,
{
	let value = match env::var(var) {
		Ok(value) => value,
		Err(env::VarError::NotPresent) => {
			return default;
		}
		Err(env::VarError::NotUnicode(err)) => {
			error!("invalid env var '{var}' value: {err:?}");
			std::process::exit(1);
		}
	};

	match value.parse::<T>() {
		Ok(parsed) => parsed,
		Err(err) => {
			error!("invalid env var '{var}' value '{value}': {err}");
			std::process::exit(1);
		}
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
	real: Rc<Box<dyn RpcClient>>,
	#[trace(skip)]
	#[allow(clippy::type_complexity)]
	key_value_cache: Rc<RefCell<BTreeMap<Vec<u8>, Option<Vec<u8>>>>>,
	fetched_prefixes: Rc<RefCell<Vec<Vec<u8>>>>,
	#[trace(skip)]
	block: Rc<String>,

	max_workers: usize,
	keys_chunk_size: usize,

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
					.buffer_unordered(self.max_workers)
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

		info!("loading keys by prefix {prefix_str}");

		let mut fetched = vec![];

		loop {
			let chunk_result = self
				.real
				.get_keys_paged(
					&prefix_str,
					self.learned_max_chunk_size.get(),
					fetched.last(),
					Some(self.block.as_ref()),
				)
				.await;

			let chunk = match chunk_result {
				Ok(v) => v,
				Err(RpcError::Server { code, message }) if code == 4002 => {
					if let Ok(v) = text_error::count_exceeds_max(&message) {
						debug!(
							"server didn't like our paged keys limit, resetting to {v}"
						);
						self.learned_max_chunk_size.set(v);
					} else {
						debug!("server didn't like our paged keys limit, and we can't extract its limit from message '{message}', reducing in half");
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
				info!("loaded {len} keys for pref {}", prefix_str);
			}
			fetched.extend(chunk);
			if !has_more {
				if !fetched.is_empty() {
					info!("loaded keys, last chunk was {len}");
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
		info!("loading key {key_str}");

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
		let progress_span = info_span!("preload_storage", indicatif.pb_show = true);
		progress_span.pb_set_style(&ProgressStyle::with_template("{msg} {wide_bar} {pos}/{len}").unwrap());
		progress_span.pb_set_length(keys.len() as u64);
		progress_span.pb_set_message("preloading keys");
		progress_span.pb_set_finish_message("all keys preloaded");

		let progress_span_guard = progress_span.enter();

		let handle = Handle::current();
		handle.block_on(
			futures::stream::iter(
				keys.chunks(self.keys_chunk_size)
					.map(|slice| self.preload_storage_fallback(progress_span.clone(), slice)),
			)
			.buffer_unordered(self.max_workers)
			.try_collect::<()>()
		)?;

		drop(progress_span_guard);
		drop(progress_span);

		info!("preloaded {} keys", keys.len());

		Ok(())
	}

	async fn preload_storage_fallback(&self, progress_span: Span, keys: &[&Vec<u8>]) -> Result<()> {
		let chunk_size = keys.len();
		match self.preload_storage_naive(progress_span.clone(), keys).await {
			Ok(()) => Ok(()),
			Err(Error::Rpc(RpcError::Server { code, .. })) if code == -32702 || code == -32008 => {
				let (keysa, keysb) = keys.split_at(chunk_size / 2);
				self.preload_storage_fallback(progress_span.clone(), keysa).boxed_local().await?;
				self.preload_storage_fallback(progress_span.clone(), keysb).boxed_local().await?;
				Ok(())
			}
			Err(err) => Err(err),
		}
	}
	async fn preload_storage_naive(&self, progress_span: Span, keys: &[&Vec<u8>]) -> Result<()> {
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

		let chunk_size = keys.len() as u64;

		let value = self
			.real
			.query_storage(list, Some(self.block.as_ref()))
			.await?;

		progress_span.pb_inc(chunk_size);

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
		info!("loading metadata");
		let handle = Handle::current();
		let meta = handle.block_on(self.real.get_metadata(Some(self.block.as_ref())))?;
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
		info!("checking for keys under {prefix:0>2x?}");
		let prefix_str = format!("0x{}", hex::encode(prefix));

		let handle = Handle::current();
		let chunk = handle.block_on(self.real.get_keys_paged(
			&prefix_str,
			1,
			None,
			Some(self.block.as_ref()),
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
}
