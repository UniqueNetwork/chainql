use jrsonnet_evaluator::{bail, runtime_error};
use jrsonnet_evaluator::{function::builtin, Result};
use sp_core::keccak_256;

use crate::hex::{to_hex, Hex};

pub fn eth_cksum_address(address: [u8; 20]) -> String {
	let address_string = to_hex(&address);
	assert!(address_string.starts_with("0x"), "sanity");
	// address string hash byte nibbles
	let ashbn = keccak_256(&address_string.as_bytes()[2..])
		.into_iter()
		.flat_map(|b| [b >> 4, b & 0b1111])
		.collect::<Vec<u8>>();
	let mut out = "0x".to_owned();
	for (bn, byte) in address.iter().enumerate() {
		for (nn, nibble) in [byte >> 4, byte & 0b1111].into_iter().enumerate() {
			let n = bn * 2 + nn;
			let ch = b"0123456789abcdef"[nibble as usize];
			out.push(if ashbn[n] >= 8 {
				ch.to_ascii_uppercase() as char
			} else {
				ch as char
			});
		}
	}
	out
}
pub fn eth_cksum_address_from_ecdsa(pubkey: [u8; 33]) -> Result<String, libsecp256k1::Error> {
	let decompressed = libsecp256k1::PublicKey::parse_compressed(&pubkey)?.serialize();
	let hashed = keccak_256(&decompressed);
	let mut address = [0u8; 20];
	address.copy_from_slice(&hashed[12..]);
	Ok(eth_cksum_address(address))
}

#[builtin]
pub fn builtin_eth_encode(address: Hex) -> Result<String> {
	Ok(match address.len() {
		20 => {
			// Address
			let mut out = [0u8; 20];
			out.copy_from_slice(&address.0);
			eth_cksum_address(out)
		}
		33 => {
			// Public key, I think user should use ethereumAddressSeed here instead, but leaving this possibility for similarity
			// with .ss58Encode
			let mut out = [0u8; 33];
			out.copy_from_slice(&address.0);
			eth_cksum_address_from_ecdsa(out).map_err(|e|runtime_error!("public key error: {e}"))?
		}
		l => bail!("ethEncode accepts either 32 bytes as ecdsa public key, or 20 bytes for ethereum address, received {l}"),
	})
}
