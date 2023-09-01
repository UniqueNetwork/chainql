use std::str::FromStr;

use jrsonnet_evaluator::{
	bail,
	jrsonnet_macros::builtin,
	runtime_error,
	typed::{CheckType, ComplexValType, Either2, Typed, ValType},
	Either, IStr, Result, Val,
};
use sp_core::{
	crypto::{SecretStringError, Ss58AddressFormat, Ss58AddressFormatRegistry, Ss58Codec},
	Pair,
};

use crate::{ethereum::eth_cksum_address_from_ecdsa, hex::Hex};

pub struct Ss58Format(pub Ss58AddressFormat);
impl Typed for Ss58Format {
	const TYPE: &'static ComplexValType = &ComplexValType::UnionRef(&[u16::TYPE, String::TYPE]);

	fn into_untyped(typed: Self) -> Result<Val> {
		match Ss58AddressFormatRegistry::try_from(typed.0) {
			Ok(r) => Ok(Val::string(r.to_string())),
			Err(_e) => Ok(Val::Num(typed.0.prefix() as f64)),
		}
	}

	fn from_untyped(untyped: Val) -> Result<Self> {
		let either = <Either![u16, String]>::from_untyped(untyped)?;
		match either {
			Either2::A(id) => Ok(Self(Ss58AddressFormat::custom(id))),
			Either2::B(name) => match Ss58AddressFormatRegistry::from_str(&name) {
				Ok(v) => Ok(Self(v.into())),
				Err(e) => bail!("unsupported address format: {e}"),
			},
		}
	}
}
impl Default for Ss58Format {
	fn default() -> Self {
		Self(Ss58AddressFormatRegistry::SubstrateAccount.into())
	}
}

#[derive(Debug, Clone, Copy)]
pub enum SignatureSchema {
	Ed25519,
	Sr25519,
	Ecdsa,
	Ethereum,
}
impl Typed for SignatureSchema {
	const TYPE: &'static ComplexValType = &ComplexValType::Simple(ValType::Str);

	fn into_untyped(typed: Self) -> jrsonnet_evaluator::Result<Val> {
		Ok(Val::Str(format!("{typed:?}").into()))
	}

	fn from_untyped(untyped: Val) -> jrsonnet_evaluator::Result<Self> {
		Self::TYPE.check(&untyped)?;
		Ok(match untyped.as_str().unwrap().as_str() {
			"Ed25519" => Self::Ed25519,
			"Sr25519" => Self::Sr25519,
			"Ecdsa" => Self::Ecdsa,
			"Ethereum" => Self::Ethereum,
			v => bail!("unknown key schema: {}", v),
		})
	}
}

pub fn address_seed(
	scheme: SignatureSchema,
	suri: &str,
	format: Ss58AddressFormat,
) -> Result<String, SecretStringError> {
	Ok(match scheme {
		SignatureSchema::Ed25519 => sp_core::ed25519::Pair::from_string_with_seed(suri, None)?
			.0
			.public()
			.to_ss58check_with_version(format),
		SignatureSchema::Sr25519 => sp_core::sr25519::Pair::from_string_with_seed(suri, None)?
			.0
			.public()
			.to_ss58check_with_version(format),
		SignatureSchema::Ecdsa => sp_core::ecdsa::Pair::from_string_with_seed(suri, None)?
			.0
			.public()
			.to_ss58check_with_version(format),
		SignatureSchema::Ethereum => {
			let (pair, _) = sp_core::ecdsa::Pair::from_string_with_seed(suri, None)?;
			eth_cksum_address_from_ecdsa(pair.public().0)
				.map_err(|_e| SecretStringError::InvalidSeed)?
		}
	})
}
pub fn public_bytes_seed(
	scheme: SignatureSchema,
	suri: &str,
) -> Result<Vec<u8>, SecretStringError> {
	let bytes = match scheme {
		SignatureSchema::Ed25519 => sp_core::ed25519::Pair::from_string_with_seed(suri, None)?
			.0
			.public()
			.0
			.to_vec(),
		SignatureSchema::Sr25519 => sp_core::sr25519::Pair::from_string_with_seed(suri, None)?
			.0
			.public()
			.0
			.to_vec(),
		SignatureSchema::Ecdsa | SignatureSchema::Ethereum => {
			sp_core::ecdsa::Pair::from_string_with_seed(suri, None)?
				.0
				.public()
				.0
				.to_vec()
		}
	};
	Ok(bytes)
}

#[builtin]
pub fn builtin_seed(scheme: SignatureSchema, suri: IStr) -> Result<Hex> {
	public_bytes_seed(scheme, &suri)
		.map_err(|e| runtime_error!("invalid seed: {e}"))
		.map(Hex)
}

#[builtin]
pub fn builtin_address_seed(
	scheme: SignatureSchema,
	suri: IStr,
	format: Option<Ss58Format>,
) -> Result<String> {
	address_seed(scheme, &suri, format.unwrap_or_default().0)
		.map_err(|e| runtime_error!("invalid seed: {e}"))
}

macro_rules! seed_helpers {
	($($(#[$attr:meta])* $fnname:ident, $fname2:ident: $schema:ident);* $(;)?) => {$(
		$(#[$attr])*
		#[builtin]
		pub fn $fnname(v: IStr) -> Result<Hex> {
			builtin_seed(SignatureSchema::$schema, v)
		}
		$(#[$attr])*
		#[builtin]
		pub fn $fname2(v: IStr, format: Option<Ss58Format>) -> Result<String> {
			builtin_address_seed(SignatureSchema::$schema, v, format)
		}
	)*};
}
seed_helpers! {
	builtin_sr25519_seed, builtin_sr25519_address_seed: Sr25519;
	builtin_ed25519_seed, builtin_ed25519_address_seed: Sr25519;
	// FIXME: Soft junctions are used in moonbeam derivation paths, but derivation function is available in
	// bip32::ExtendedPrivateKey, which moonbeam folks are using instead of substrate apis:
	// https://github.com/moonbeam-foundation/moonbeam/blob/a395d45c71e0575414ac13fdcb531d877131fde9/node/service/src/chain_spec/mod.rs#L89-L115
	/// Soft junctions are not supported (I.e /m/0/...), thus you may not be able to derive public key from seeds using them.
	builtin_ecdsa_seed, builtin_ecdsa_address_seed: Ecdsa;
	/// Soft junctions are not supported (I.e /m/0/...), thus you may not be able to derive public key from seeds using them.
	/// Accepts an optional `Ss58Format` argument, but it isn't used, it is only left for consistency, ethereum addresses
	/// do not use ss58 encoding.
	builtin_ethereum_seed, builtin_ethereum_address_seed: Ethereum;
}
