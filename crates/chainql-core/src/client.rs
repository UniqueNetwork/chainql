use std::{rc::Rc, result};

use frame_metadata::RuntimeMetadataV14;
use jrsonnet_evaluator::runtime_error;
use jrsonnet_gcmodule::Trace;

pub mod dump;
pub mod live;

#[derive(thiserror::Error, Debug)]
pub enum Error {
	#[error("live: {0}")]
	Live(#[from] live::Error),
	#[error("dump: {0}")]
	Dump(#[from] dump::Error),
}
type Result<T, E = Error> = result::Result<T, E>;

impl From<Error> for jrsonnet_evaluator::Error {
	fn from(value: Error) -> Self {
		runtime_error!("client: {value}")
	}
}

pub trait ClientT {
	fn get_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>>;
	fn get_unknown_keys(&self, prefix: &[u8], known_prefixes: &[&Vec<u8>]) -> Result<Vec<Vec<u8>>> {
		let keys = self.get_keys(prefix)?;
		assert!(
			known_prefixes.iter().all(|p| !p.is_empty()),
			"known prefix can't be empty"
		);
		Ok(keys
			.into_iter()
			.filter(|key| known_prefixes.iter().all(|known| !key.starts_with(known)))
			.collect())
	}
	fn get_storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>>;
	fn preload_storage(&self, keys: &[&Vec<u8>]) -> Result<()>;
	fn get_metadata(&self) -> Result<RuntimeMetadataV14>;
	fn contains_data_for(&self, prefix: &[u8]) -> Result<bool>;
	fn contains_key(&self, key: &[u8]) -> Result<bool> {
		Ok(self.get_storage(key)?.is_some())
	}
	fn next(&self) -> Result<Client>;
}

#[derive(Clone, Trace)]
pub struct Client(#[trace(skip)] Rc<dyn ClientT>);
impl Client {
	pub fn new<V: ClientT + 'static>(v: V) -> Self {
		Self(Rc::new(v))
	}
}
impl ClientT for Client {
	fn get_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>> {
		self.0.get_keys(prefix)
	}

	fn get_storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
		self.0.get_storage(key)
	}

	fn preload_storage(&self, keys: &[&Vec<u8>]) -> Result<()> {
		self.0.preload_storage(keys)
	}

	fn get_metadata(&self) -> Result<RuntimeMetadataV14> {
		self.0.get_metadata()
	}

	fn contains_data_for(&self, prefix: &[u8]) -> Result<bool> {
		self.0.contains_data_for(prefix)
	}

	fn next(&self) -> Result<Client> {
		self.0.next()
	}
}
