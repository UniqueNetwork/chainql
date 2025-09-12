use futures::FutureExt;
use reqwest::StatusCode;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sp_runtime::DeserializeOwned;
use tokio::{
	sync::Mutex,
	time::{sleep, Duration, Instant},
};

use crate::client::rpc::{QueryStorageResult, Result, Rpc, RpcError};

#[derive(Deserialize)]
pub struct Response<T> {
	result: Option<T>,
	error: Option<ResponseError>,
}

#[derive(Deserialize)]
pub struct ResponseError {
	code: i32,
	message: String,
}

pub struct HttpClient {
	client: reqwest::Client,
	url: reqwest::Url,
	rate_limiter: RateLimiter,
}

impl HttpClient {
	pub fn new(url: reqwest::Url, timeout: Duration) -> Result<Self> {
		Ok(Self {
			client: reqwest::Client::builder().timeout(timeout).build()?,
			url: url,
			rate_limiter: RateLimiter::new(),
		})
	}

	async fn call<T: DeserializeOwned>(&self, method: &str, params: &impl Serialize) -> Result<T> {
		self.rate_limiter.wait().await;

		let body = serde_json::json!({
			"jsonrpc": "2.0",
			"id": null,
			"method": method,
			"params": params,
		});

		let response = self
			.client
			.post(self.url.clone())
			.json(&body)
			.send()
			.await?;

		if response.status() == StatusCode::TOO_MANY_REQUESTS
			|| response.status() == StatusCode::GATEWAY_TIMEOUT
		{
			self.rate_limiter.request_limited().await;
			return self.call(method, params).boxed_local().await;
		} else {
			self.rate_limiter.request_succeeded().await;
		}

		if response.status() != StatusCode::OK {
			return Err(RpcError::BadResponse(format!(
				"unexpected status code {}",
				response.status()
			)));
		}

		let response_body = response.text().await?;

		let deserialized = serde_json::from_str::<Response<T>>(&response_body)
			.map_err(|err| RpcError::BadResponse(err.to_string()))?;

		if let Some(result) = deserialized.result {
			Ok(result)
		} else if let Some(e) = deserialized.error {
			Err(RpcError::Server {
				code: e.code,
				message: e.message,
			})
		} else {
			Err(RpcError::BadResponse(format!(
				"no error or result in json '{response_body}'"
			)))
		}
	}
}

impl Rpc for HttpClient {
	async fn get_block_hash(&self, num: Option<u32>) -> Result<Option<String>> {
		self.call(
			"chain_getBlockHash",
			&json!({
				"num": num
			}),
		)
		.await
	}

	async fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> Result<Vec<String>> {
		self.call(
			"state_getKeysPaged",
			&json!({
				"key": key,
				"count": count,
				"start_key": start_key,
				"at": at
			}),
		)
		.await
	}

	async fn get_storage(&self, key: String, at: Option<String>) -> Result<Option<String>> {
		self.call(
			"state_getStorage",
			&json!({
				"key": key,
				"at": at
			}),
		)
		.await
	}

	async fn query_storage(
		&self,
		keys: Vec<String>,
		at: Option<&String>,
	) -> Result<Vec<QueryStorageResult>> {
		self.call(
			"state_queryStorageAt",
			&json!({
				"keys": keys,
				"at": at
			}),
		)
		.await
	}

	async fn get_metadata(&self, at: Option<&String>) -> Result<String> {
		self.call(
			"state_getMetadata",
			&json!({
				"at": at
			}),
		)
		.await
	}
}

struct RateLimiter(Mutex<RateLimiterState>);

struct RateLimiterState {
	rps: u32,
	increase_param: u32,
	decrease_factor: f32,
	last_requested_at: Option<Instant>,
}

impl RateLimiter {
	fn new() -> Self {
		Self(Mutex::new(RateLimiterState {
			rps: 1000,
			increase_param: 50,
			decrease_factor: 0.8,
			last_requested_at: None,
		}))
	}

	async fn wait(&self) {
		let requested_at = Instant::now();

		let sleep_duration = {
			let mut this = self.0.lock().await;

			if let Some(last_requested_at) = this.last_requested_at.replace(requested_at) {
				(Duration::from_secs(60) / this.rps)
					.saturating_sub(requested_at - last_requested_at)
			} else {
				Duration::ZERO
			}
		};

		sleep(sleep_duration).await
	}

	async fn request_succeeded(&self) {
		let mut this = self.0.lock().await;

		this.rps += this.increase_param;
	}

	async fn request_limited(&self) {
		let mut this = self.0.lock().await;

		let new_rps = ((this.rps as f32) * this.decrease_factor).round() as u32;

		this.rps = if new_rps > 0 { new_rps } else { 1 };
	}
}
