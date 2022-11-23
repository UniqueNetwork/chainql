use std::{rc::Rc, result};

use frame_metadata::RuntimeMetadataV14;
use jrsonnet_gcmodule::Trace;

pub mod dump;
pub mod live;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("live: {0}")]
    Live(#[from] live::Error),
}
type Result<T, E = Error> = result::Result<T, E>;

pub trait ClientT {
    fn get_keys(&self, prefix: &[u8]) -> Result<Vec<Vec<u8>>>;
    fn get_storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>>;
    fn preload_storage(&self, keys: &[&Vec<u8>]) -> Result<()>;
    fn get_metadata(&self) -> Result<RuntimeMetadataV14>;
    fn contains_data_for(&self, prefix: &[u8]) -> Result<bool>;
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
}
