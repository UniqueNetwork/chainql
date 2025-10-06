use async_trait::async_trait;
use reqwest::StatusCode;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sp_runtime::DeserializeOwned;
use std::sync::Mutex;
use tokio::time::{sleep, Duration, Instant};

use crate::client::rpc::{QueryStorageResult, Result, RpcClient, RpcError};

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

	async fn call<P, T>(&self, method: &'static str, params: P) -> Result<T>
	where
		P: Serialize,
		T: DeserializeOwned,
	{
		let mut rate_limiter_guard = self.rate_limiter.request_pending().await;

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

		if [
			StatusCode::TOO_MANY_REQUESTS,
			StatusCode::PAYLOAD_TOO_LARGE,
			StatusCode::GATEWAY_TIMEOUT,
		]
		.contains(&response.status())
		{
			drop(rate_limiter_guard);
			return Box::pin(self.call(method, params)).await;
		}

		rate_limiter_guard.succeeded();

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

#[async_trait]
impl RpcClient for HttpClient {
	async fn get_block_hash(&self, num: Option<u32>) -> Result<Option<String>> {
		self.call("chain_getBlockHash", json!([num])).await
	}

	async fn get_keys_paged(
		&self,
		key: &String,
		count: usize,
		start_key: Option<&String>,
		at: Option<&String>,
	) -> Result<Vec<String>> {
		self.call("state_getKeysPaged", json!([key, count, start_key, at]))
			.await
	}

	async fn get_storage(&self, key: String, at: Option<String>) -> Result<Option<String>> {
		self.call("state_getStorage", json!([key, at])).await
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
		self.call("state_getMetadata", json!([at])).await
	}
}

struct RateLimiter(Mutex<RateLimiterState>);

struct RateLimiterState {
	rpm: u32,
	increase_param: u32,
	decrease_factor: f32,
	last_requested_at: Option<Instant>,
}

impl RateLimiter {
	fn new() -> Self {
		Self(Mutex::new(RateLimiterState {
			rpm: 1000,
			increase_param: 50,
			decrease_factor: 0.8,
			last_requested_at: None,
		}))
	}

	async fn wait(&self) {
		let requested_at = Instant::now();

		let sleep_duration = {
			let mut this = self.0.lock().expect("not poisoned");

			if let Some(last_requested_at) = this.last_requested_at.replace(requested_at) {
				(Duration::from_secs(60) / this.rpm)
					.saturating_sub(requested_at - last_requested_at)
			} else {
				Duration::ZERO
			}
		};

		sleep(sleep_duration).await
	}

	async fn request_pending(&self) -> RateLimiterGuard<'_> {
		self.wait().await;

		RateLimiterGuard {
			rate_limiter: self,
			succeeded: false,
		}
	}

	fn request_succeeded(&self) {
		let mut this = self.0.lock().expect("not poisoned");

		this.rpm += this.increase_param;
	}

	fn request_limited(&self) {
		let mut this = self.0.lock().expect("not poisoned");

		let new_rps = ((this.rpm as f32) * this.decrease_factor).floor() as u32;

		this.rpm = new_rps.max(1);
	}
}

struct RateLimiterGuard<'a> {
	rate_limiter: &'a RateLimiter,
	succeeded: bool,
}

impl RateLimiterGuard<'_> {
	fn succeeded(&mut self) {
		self.succeeded = true;
	}
}

impl Drop for RateLimiterGuard<'_> {
	fn drop(&mut self) {
		if self.succeeded {
			self.rate_limiter.request_succeeded();
		} else {
			self.rate_limiter.request_limited();
		}
	}
}
