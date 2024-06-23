use std::borrow::Cow;
use std::path::{Path, PathBuf};

use jrsonnet_evaluator::{
	error::ErrorKind::RuntimeError, function::builtin, typed::Typed, val::ThunkValue, ObjValue,
	Result, Val,
};
use jrsonnet_gcmodule::{Cc, Trace};
use parity_scale_codec::Decode;
use sc_executor::{RuntimeVersionOf, WasmExecutor};
use sp_core::blake2_256;
use sp_core::traits::{CodeExecutor, RuntimeCode, WrappedRuntimeCode};

type HostFunctions = (sp_io::SubstrateHostFunctions, cumulus_primitives_proof_size_hostfunction::storage_proof_size::HostFunctions);

use crate::Hex;

#[derive(Trace)]
pub struct RuntimeContainer {
	#[trace(skip)]
	code: WrappedRuntimeCode<'static>,
	#[trace(skip)]
	hash: [u8; 32],
	#[trace(skip)]
	executor: WasmExecutor<HostFunctions>,
}

#[derive(Typed)]
pub struct RuntimeVersion {
	spec_name: String,
	spec_version: u32,
	state_version: u8,
	transaction_version: u32,
}

impl RuntimeContainer {
	pub fn new(code: Vec<u8>, cache_path: Option<&Path>) -> Self {
		let mut executor = <WasmExecutor<HostFunctions>>::builder()
			// chainql is single-threaded
			.with_max_runtime_instances(1);
		if let Some(cache_path) = cache_path {
			executor = executor.with_cache_path(cache_path);
		};
		let executor = executor.build();
		Self {
			hash: blake2_256(&code),
			code: WrappedRuntimeCode(Cow::Owned(code)),
			executor,
		}
	}
	fn runtime_code(&self) -> RuntimeCode<'_> {
		RuntimeCode {
			code_fetcher: &self.code,
			heap_pages: Some(100),
			hash: self.hash.to_vec(),
		}
	}
	pub fn version(&self) -> Result<RuntimeVersion> {
		let mut ext = sp_state_machine::BasicExternalities::new_empty();
		let version =
			RuntimeVersionOf::runtime_version(&self.executor, &mut ext, &self.runtime_code())
				.map_err(|e| RuntimeError(format!("{e}").into()))?;

		Ok(RuntimeVersion {
			spec_name: version.spec_name.to_string(),
			spec_version: version.spec_version,
			state_version: version.state_version,
			transaction_version: version.transaction_version,
		})
	}
	pub fn metadata(&self) -> Result<Vec<u8>> {
		let mut ext = sp_state_machine::BasicExternalities::new_empty();
		let (result, _native_used) = self.executor.call(
			&mut ext,
			&self.runtime_code(),
			"Metadata_metadata",
			&[],
			sp_core::traits::CallContext::Onchain,
		);
		let result = result.expect("metadata is implemented for substrate chains");
		let result = <Vec<u8>>::decode(&mut result.as_slice()).expect("valid output");
		Ok(result)
	}
}

#[builtin(fields(
	cache_path: Option<PathBuf>,
))]
pub fn builtin_runtime_wasm(this: &builtin_runtime_wasm, data: Hex) -> Result<ObjValue> {
	let runtime = Cc::new(RuntimeContainer::new(data.0, this.cache_path.as_deref()));

	#[derive(Trace)]
	struct RuntimeVersionThunk {
		runtime: Cc<RuntimeContainer>,
	}
	impl ThunkValue for RuntimeVersionThunk {
		type Output = Val;
		fn get(self: Box<Self>) -> Result<Val> {
			RuntimeVersion::into_untyped(self.runtime.version()?)
		}
	}
	#[derive(Trace)]
	struct MetadataThunk {
		runtime: Cc<RuntimeContainer>,
	}
	impl ThunkValue for MetadataThunk {
		type Output = Val;
		fn get(self: Box<Self>) -> Result<Val> {
			self.runtime.metadata().map(Hex).and_then(Hex::into_untyped)
		}
	}

	let mut out = ObjValue::builder();

	out.field("version").thunk(RuntimeVersionThunk {
		runtime: runtime.clone(),
	})?;
	out.field("metadata").thunk(MetadataThunk {
		runtime: runtime.clone(),
	})?;

	Ok(out.build())
}
