use async_trait::async_trait;
use reqwest::StatusCode;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sp_runtime::DeserializeOwned;
use std::sync::Mutex;
use tokio::time::{Duration, Instant, sleep};

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
	const RATE_LIMITED_STATUSES: &[StatusCode] =
		&[StatusCode::TOO_MANY_REQUESTS, StatusCode::GATEWAY_TIMEOUT];

	pub fn new(url: reqwest::Url, timeout: Duration) -> Result<Self> {
		Ok(Self {
			client: reqwest::Client::builder().timeout(timeout).build()?,
			url: url,
			rate_limiter: RateLimiter::new(),
		})
	}

	async fn call_non_none<P, T>(&self, method: &str, params: P) -> Result<T>
	where
		P: Serialize,
		T: DeserializeOwned,
	{
		self.call(method, params)
			.await?
			.ok_or_else(|| RpcError::BadResponse("unexpected null from server".to_owned()))
	}

	async fn call<P, T>(&self, method: &str, params: P) -> Result<Option<T>>
	where
		P: Serialize,
		T: DeserializeOwned,
	{
		let response = self.request(method, &params).await?;

		if Self::RATE_LIMITED_STATUSES.contains(&response.status()) {
			return Box::pin(self.call(method, params)).await;
		}

		self.status_to_error(&response)?;

		let response_body = response.text().await?;

		let deserialized = serde_json::from_str::<Response<T>>(&response_body)
			.map_err(|err| RpcError::BadResponse(err.to_string()))?;

		if let Some(e) = deserialized.error {
			return Err(RpcError::Server {
				code: e.code,
				message: e.message,
			});
		}

		return Ok(deserialized.result);
	}

	async fn request(&self, method: &str, params: &impl Serialize) -> Result<reqwest::Response> {
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

		if !Self::RATE_LIMITED_STATUSES.contains(&response.status()) {
			rate_limiter_guard.succeeded();
		}

		Ok(response)
	}

	fn status_to_error(&self, response: &reqwest::Response) -> Result<()> {
		match response.status() {
			StatusCode::OK => Ok(()),
			StatusCode::PAYLOAD_TOO_LARGE => Err(RpcError::Server {
				code: 4002,
				message: "request limit exceeded at http level (status code 413)".to_owned(),
			}),
			other => Err(RpcError::BadResponse(format!(
				"unexpected status code {other}",
			))),
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
		self.call_non_none("state_getKeysPaged", json!([key, count, start_key, at]))
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
		self.call_non_none(
			"state_queryStorageAt",
			json!({
				"keys": keys,
				"at": at
			}),
		)
		.await
	}

	async fn get_metadata(&self, at: Option<&String>) -> Result<String> {
		self.call_non_none("state_getMetadata", json!([at])).await
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
