use std::{borrow::Cow, rc::Rc};

use jrsonnet_evaluator::{
	error::ErrorKind::RuntimeError, function::builtin, typed::Typed, val::ThunkValue, ObjValue,
	Result, Thunk, Val,
};
use jrsonnet_gcmodule::{Cc, Trace};
use parity_scale_codec::Decode;
use sc_executor::{RuntimeVersionOf, WasmExecutor};
use sp_core::traits::{CodeExecutor, RuntimeCode, WrappedRuntimeCode};
use sp_io::SubstrateHostFunctions;

use crate::Hex;

#[derive(Trace)]
pub struct RuntimeContainer {
	#[trace(skip)]
	code: WrappedRuntimeCode<'static>,
	#[trace(skip)]
	executor: WasmExecutor<SubstrateHostFunctions>,
}

#[derive(Typed)]
pub struct RuntimeVersion {
	spec_name: String,
	spec_version: u32,
	state_version: u8,
	transaction_version: u32,
}

impl RuntimeContainer {
	pub fn new(code: Vec<u8>) -> Self {
		Self {
			code: WrappedRuntimeCode(Cow::Owned(code)),
			executor: <WasmExecutor<SubstrateHostFunctions>>::builder().build(),
		}
	}
	fn runtime_code(&self) -> RuntimeCode<'_> {
		RuntimeCode {
			code_fetcher: &self.code,
			heap_pages: Some(100),
			hash: Vec::new(),
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
			false,
			sp_core::traits::CallContext::Onchain,
		);
		let result = result.expect("metadata is implemented for substrate chains");
		let result = <Vec<u8>>::decode(&mut result.as_slice()).expect("valid output");
		Ok(result)
	}
}

#[builtin]
pub fn builtin_runtime_wasm(data: Hex) -> Result<ObjValue> {
	let runtime = Cc::new(RuntimeContainer::new(data.0));

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

	out.member("version".into())
		.thunk(Thunk::new(RuntimeVersionThunk {
			runtime: runtime.clone(),
		}))?;
	out.member("metadata".into())
		.thunk(Thunk::new(MetadataThunk {
			runtime: runtime.clone(),
		}))?;

	Ok(out.build())
}
