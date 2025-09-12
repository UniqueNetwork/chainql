use async_trait::async_trait;
use serde::Deserialize;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RpcError {
	#[error("reqwest error: {0}")]
	Reqwest(#[from] reqwest::Error),

	#[error("jsonrpsee error: {0}")]
	Jsonrpsee(#[from] jsonrpsee::core::ClientError),

	#[error("bad response: {0}")]
	BadResponse(String),

	#[error("jsonrpc error: {message} (code {code})")]
	Server { code: i32, message: String },
}

pub type Result<T, E = RpcError> = core::result::Result<T, E>;

#[derive(Deserialize)]
pub struct QueryStorageResult {
	pub changes: Vec<(String, Option<String>)>,
}

#[async_trait]
pub trait RpcClient {
	async fn get_block_hash(&self, num: Option<u32>) -> Result<Option<String>>;

	async fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> Result<Vec<String>>;

	async fn get_storage(&self, key: String, at: Option<String>) -> Result<Option<String>>;

	async fn query_storage(
		&self,
		keys: Vec<String>,
		at: Option<&String>,
	) -> Result<Vec<QueryStorageResult>>;

	async fn get_metadata(&self, at: Option<&String>) -> Result<String>;
}
