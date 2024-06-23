use std::{borrow::Borrow, ops::Deref};

use jrsonnet_evaluator::{
	function::builtin,
	runtime_error,
	typed::{CheckType, ComplexValType, Typed, ValType},
	Result, Val,
};

use crate::ensure;

#[derive(Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Hex(pub Vec<u8>);
impl Hex {
	pub fn encode_str(str: &str) -> Self {
		Self(str.as_bytes().into())
	}
}
impl Typed for Hex {
	const TYPE: &'static ComplexValType = &ComplexValType::Simple(ValType::Str);

	fn into_untyped(typed: Self) -> Result<Val> {
		Ok(Val::Str(to_hex(&typed.0).into()))
	}

	fn from_untyped(untyped: Val) -> Result<Self> {
		Self::TYPE.check(&untyped)?;
		let str = untyped.as_str().expect("is string");
		Ok(Self(from_hex(&str)?))
	}
}
impl Borrow<[u8]> for Hex {
	fn borrow(&self) -> &[u8] {
		&self.0
	}
}
impl Deref for Hex {
	type Target = [u8];

	fn deref(&self) -> &Self::Target {
		self.0.as_slice()
	}
}

/// Convert an array of bytes to a hex string.
pub fn to_hex(data: &[u8]) -> String {
	let mut out = vec![0; data.len() * 2 + 2];
	out[0] = b'0';
	out[1] = b'x';
	hex::encode_to_slice(data, &mut out[2..]).expect("size is correct");
	String::from_utf8(out).expect("hex is utf-8 compatible")
}

/// Convert a hex string to a vector of bytes.
pub fn from_hex(data: &str) -> Result<Vec<u8>> {
	ensure!(data.starts_with("0x"), "string doesn't starts with 0x");
	let out = hex::decode(&data.as_bytes()[2..])
		.map_err(|e| runtime_error!("failed to decode hex: {e}"))?;
	Ok(out)
}

/// Convert an array of bytes to a hex string.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```text
/// cql.toHex([0, 0, 0, 2, 16, 62, 200, 1]) == "0x00000002103ec801"
/// ```
#[builtin]
pub fn builtin_to_hex(data: Vec<u8>) -> Result<Hex> {
	Ok(Hex(data))
}

/// Convert a hex string to a vector of bytes.
///
/// This function is passed to Jsonnet and is callable from the code.
///
/// # Example
///
/// ```text
/// cql.fromHex("0x00000002103ec801") == [0, 0, 0, 2, 16, 62, 200, 1]
/// ```
#[builtin]
pub fn builtin_from_hex(data: Hex) -> Vec<u8> {
	data.0
}
