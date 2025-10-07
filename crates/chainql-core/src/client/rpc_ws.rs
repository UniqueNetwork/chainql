use async_trait::async_trait;
use jsonrpsee::proc_macros::rpc;
use tokio::time::Duration;

use crate::client::rpc::{QueryStorageResult, Result, RpcClient, RpcError};

#[rpc(client)]
pub trait SubstrateRpc {
	#[method(name = "chain_getBlockHash")]
	fn get_block_hash(&self, num: Option<u32>) -> RpcResult<Option<String>>;

	#[method(name = "state_getKeysPaged")]
	fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> RpcResult<Vec<String>>;

	#[method(name = "state_getStorage")]
	fn get_storage(&self, key: String, at: Option<String>) -> RpcResult<Option<String>>;

	#[method(name = "state_queryStorageAt")]
	fn query_storage(
		&self,
		keys: Vec<String>,
		at: Option<&String>,
	) -> RpcResult<Vec<QueryStorageResult>>;

	#[method(name = "state_getMetadata")]
	fn get_metadata(&self, at: Option<&String>) -> RpcResult<String>;
}

pub struct WsClient {
	client: jsonrpsee::ws_client::WsClient,
}

impl WsClient {
	pub async fn new(url: reqwest::Url, timeout: Duration) -> Result<Self> {
		Ok(Self {
			client: jsonrpsee::ws_client::WsClientBuilder::default()
				.request_timeout(timeout)
				.max_request_size(256 * 1024 * 1024)
				.max_response_size(1024 * 1024 * 1024)
				.build(url.to_string())
				.await?,
		})
	}
}

fn convert_error(err: jsonrpsee::core::ClientError) -> RpcError {
	match err {
		jsonrpsee::core::ClientError::Call(err) => RpcError::Server {
			code: err.code(),
			message: err.message().to_owned(),
		},
		_ => RpcError::Jsonrpsee(err),
	}
}

#[async_trait]
impl RpcClient for WsClient {
	async fn get_block_hash(&self, num: Option<u32>) -> Result<Option<String>> {
		self.client.get_block_hash(num).await.map_err(convert_error)
	}

	async fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> Result<Vec<String>> {
		self.client
			.get_keys_paged(key, count, start_key, at)
			.await
			.map_err(convert_error)
	}

	async fn get_storage(&self, key: String, at: Option<String>) -> Result<Option<String>> {
		self.client
			.get_storage(key, at)
			.await
			.map_err(convert_error)
	}

	async fn query_storage(
		&self,
		keys: Vec<String>,
		at: Option<&String>,
	) -> Result<Vec<QueryStorageResult>> {
		self.client
			.query_storage(keys, at)
			.await
			.map_err(convert_error)
	}

	async fn get_metadata(&self, at: Option<&String>) -> Result<String> {
		self.client.get_metadata(at).await.map_err(convert_error)
	}
}
