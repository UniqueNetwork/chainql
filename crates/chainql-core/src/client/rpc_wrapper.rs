use async_trait::async_trait;
use tracing::warn;

use crate::client::rpc::{QueryStorageResult, Result, RpcClient, RpcError};

pub struct RetryClient {
	client: Box<dyn RpcClient + Send + Sync + 'static>,
	max_attemps: usize,
}

impl RetryClient {
	pub fn new<C>(client: C, retries: usize) -> Self
	where
		C: RpcClient + Send + Sync + 'static,
	{
		Self {
			client: Box::new(client),
			max_attemps: retries,
		}
	}
}

macro_rules! retry {
	($max_attemps:expr, $method:expr) => {
		if $max_attemps < 2 {
			return $method;
		} else {
			let mut last_error = None;
			for _ in 0..$max_attemps {
				match $method {
					Ok(result) => {
						return Ok(result);
					},
					Err(err @ RpcError::Server { .. }) => {
						return Err(err);
					},
					Err(err) => {
						warn!("failed to execute {}: {}", stringify!($method), err);
						last_error = Some(err);
					},
				}
			}
			return Err(RpcError::AttemptsFailed {
				attemps: $max_attemps,
				error: Box::new(last_error.unwrap()),
			});
		}
	};
}

#[async_trait]
impl RpcClient for RetryClient {
	async fn get_block_hash(&self, num: Option<u32>) -> Result<Option<String>> {
		retry!(
			self.max_attemps,
			self.client.get_block_hash(num).await
		);
	}

	async fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> Result<Vec<String>> {
		retry!(
			self.max_attemps,
			self.client.get_keys_paged(key, count, start_key, at).await
		);
	}

	async fn get_storage(&self, key: String, at: Option<String>) -> Result<Option<String>> {
		retry!(
			self.max_attemps,
			self.client.get_storage(key.clone(), at.clone()).await
		);
	}

	async fn query_storage(
		&self,
		keys: Vec<String>,
		at: Option<&String>,
	) -> Result<Vec<QueryStorageResult>> {
		retry!(
			self.max_attemps, 
			self.client.query_storage(keys.clone(), at).await
		);
	}

	async fn get_metadata(&self, at: Option<&String>) -> Result<String> {
		retry!(
			self.max_attemps, 
			self.client.get_metadata(at).await
		);
	}
}
