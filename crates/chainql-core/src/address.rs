use std::str::FromStr;

use jrsonnet_evaluator::{
	bail, jrsonnet_macros::builtin, runtime_error, typed::{CheckType, ComplexValType, Either2, Typed, ValType}, val::NumValue, Either, IStr, ObjValue, Result, ResultExt, Val
};
use sp_core::{
	crypto::{SecretStringError, Ss58AddressFormat, Ss58AddressFormatRegistry, Ss58Codec},
	ecdsa, ed25519, keccak_256, sr25519, Pair,
};
use sp_runtime::{traits::Verify, AccountId32, MultiSignature};

use crate::{ensure, ethereum::eth_cksum_address_from_ecdsa, hex::Hex};

pub struct Ss58Format(pub Ss58AddressFormat);
impl Typed for Ss58Format {
	const TYPE: &'static ComplexValType = &ComplexValType::UnionRef(&[u16::TYPE, String::TYPE]);

	fn into_untyped(typed: Self) -> Result<Val> {
		match Ss58AddressFormatRegistry::try_from(typed.0) {
			Ok(r) => Ok(Val::string(r.to_string())),
			Err(_e) => Ok(Val::Num(NumValue::new(typed.0.prefix() as f64).unwrap())),
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
		SignatureSchema::Ed25519 => ed25519::Pair::from_string_with_seed(suri, None)?
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
		SignatureSchema::Ed25519 => ed25519::Pair::from_string_with_seed(suri, None)?
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

#[derive(Clone, Copy)]
pub enum SignatureType {
	MultiSignature,
	Plain(SignatureSchema),
}
#[derive(Clone, PartialEq)]
pub enum AddressSchema {
	Id32,
	Id20,
}
#[derive(Clone)]
pub enum AddressType {
	MultiAddress { default: AddressSchema },
	Plain(AddressSchema),
}
pub fn verify_signature(
	signature_ty: SignatureType,
	signature: Val,
	address_ty: AddressType,
	address: Val,
	data: Hex,
) -> Result<bool> {
	let (signature_ty, signature) = match signature_ty {
		SignatureType::MultiSignature => {
			let sign = ObjValue::from_untyped(signature).description("multisignature obj")?;
			let fields = sign.fields(false);
			if fields.len() != 1 {
				bail!("multisignature is enum");
			};
			let plain = match fields[0].as_str() {
				"Ed25519" => SignatureSchema::Ed25519,
				"Sr25519" => SignatureSchema::Sr25519,
				"Ecdsa" => SignatureSchema::Ecdsa,
				s => bail!("unknown multisignature type: {s}"),
			};
			let value = sign
				.get(fields[0].clone())
				.description("signature value")?
				.expect("exists");
			(
				plain,
				Hex::from_untyped(value).description("multisig value")?.0,
			)
		}
		SignatureType::Plain(s) => (s, Hex::from_untyped(signature).description("signature")?.0),
	};

	let (address_ty, address) = match address_ty {
		AddressType::MultiAddress { default } => {
			let addr = ObjValue::from_untyped(address).description("multiaddress obj")?;
			let fields = addr.fields(false);
			if fields.len() != 1 {
				bail!("multiaddress is enum");
			};
			let ty = fields[0].as_str();
			if ty == "Address32" || ty == "Id" && default == AddressSchema::Id32 {
				let value = addr
					.get(ty.into())
					.description("address value")?
					.expect("exists");
				(
					AddressSchema::Id32,
					Hex::from_untyped(value).description("multiaddr value")?.0,
				)
			} else {
				bail!("unknown multiaddress type: {ty}");
			}
		}
		AddressType::Plain(_) => todo!(),
	};

	if let SignatureSchema::Ethereum = signature_ty {
		ensure!(
			address_ty == AddressSchema::Id20,
			"ethereum address schema should be id20"
		);
		let address: [u8; 20] = address
			.try_into()
			.map_err(|e| runtime_error!("bad ethereum address: {e:?}"))?;
		let hash = keccak_256(&data);
		let ecdsa_sign = signature
			.try_into()
			.map_err(|e| runtime_error!("bad ethereum signature: {e:?}"))?;
		match sp_io::crypto::secp256k1_ecdsa_recover(&ecdsa_sign, &hash) {
			Ok(pubkey) => {
				let pubkey_hash = keccak_256(&pubkey);
				let mut expected_address = [0; 20];
				expected_address.copy_from_slice(&pubkey_hash[12..32]);
				return Ok(expected_address == address);
			}
			Err(_) => return Ok(false),
		}
	}

	let multisig = match signature_ty {
		SignatureSchema::Ed25519 => MultiSignature::Ed25519(ed25519::Signature::from_raw(
			signature
				.try_into()
				.map_err(|e| runtime_error!("bad ecdsa signature: {e:?}"))?,
		)),
		SignatureSchema::Sr25519 => MultiSignature::Sr25519(sr25519::Signature::from_raw(
			signature
				.try_into()
				.map_err(|e| runtime_error!("bad sr25519 signature: {e:?}"))?,
		)),
		SignatureSchema::Ecdsa => MultiSignature::Ecdsa(ecdsa::Signature::from_raw(
			signature
				.try_into()
				.map_err(|e| runtime_error!("bad ecdsa signature: {e:?}"))?,
		)),
		SignatureSchema::Ethereum => unreachable!("has special handling"),
	};

	ensure!(
		address_ty == AddressSchema::Id32,
		"substrate address schema should be id32"
	);
	let address: [u8; 32] = address
		.try_into()
		.map_err(|e| runtime_error!("bad accountid32: {e:?}"))?;
	let id32 = AccountId32::new(address);
	Ok(multisig.verify(data.0.as_slice(), &id32))
}
