// Get live chain data on the URL provided with `forkFrom`, and 
// insert the necessary data into a chain spec to launch a new chain with.
// 
// ### Arguments
// - `rawSpec`: Path to the raw chain spec to modify
// - `forkFrom`: URL of the chain's WS port to get the data from
// 
// ### Usage
// `chainql --tla-code=rawSpec="import 'parachain-spec-raw.json'" --tla-str=forkFrom="wss://some-parachain.node:443" fork.jsonnet`

function(rawSpec, forkFrom)
local sourceChain = cql.chain(forkFrom).latest;

// Load the data to encode into the chain spec and filter out the empty entries
local raw = local sourceRaw = sourceChain._raw._preloadKeys; {
  [key]: cql.toHex(sourceRaw[key])
  for key in std.objectFields(sourceRaw)
  if sourceRaw[key] != null
};

// Categorize the types for decoding used on the source chain, using the function present in another file
local typeNames = (import './typeNames.jsonnet')(sourceChain);

local
auraKeys = [
	// AuraExt.Authorities, we don't have aura pallet enabled for some reason, to refer using cql api
	'0x3c311d57d4daf52904616cf69648081e5e0621c4869aa60c02be9adcc98a0d1d',
	// Aura.Authorities
	'0x57f8dc2f5ab09467896f47300f0424385e0621c4869aa60c02be9adcc98a0d1d',
],

// Keys, the values of which should be taken from the passed spec rather than from the forked chain
wantedKeys = [
	sourceChain.ParachainInfo._key.ParachainId,
	sourceChain.Sudo._key.Key,
	sourceChain.System.BlockHash._key['0'],
	sourceChain.System._key.ParentHash,
] + auraKeys,

// Keys to remove from the chain spec
unwantedPrefixes = [
	// Aura.CurrentSlot
	'0x57f8dc2f5ab09467896f47300f04243806155b3cd9a8c9e5e9a23fd5dc13a5ed',
	// Ensure there will be no panics caused by unexpected kept state
	sourceChain.ParachainSystem._key.ValidationData,
	sourceChain.ParachainSystem._key.RelayStateProof,
	sourceChain.ParachainSystem._key.HostConfiguration,
	sourceChain.ParachainSystem._key.LastDmqMqcHead,
	// Part of head
	sourceChain.System._key.BlockHash,
	sourceChain.System._key.Number,
	sourceChain.System._key.Digest,
] + auraKeys,

// Function to remove unwanted keys from the chain spec
cleanupRaw(raw) = {
	[key]: raw[key]
	for key in std.objectFields(raw)
	if std.all(std.map(function(prefix) !std.startsWith(key, prefix), unwantedPrefixes))
};

local originalRaw = rawSpec.genesis.raw.top;
// Remove unwanted keys from the chain spec and leave the original keys, if they are wanted
local outSpec = rawSpec {
	genesis+: {
		raw+: {
			// Replace the `top` section with the cleaned-up spec
			top: cleanupRaw(raw) {
				[key]: originalRaw[key]
				for key in wantedKeys
				if std.objectHas(originalRaw, key)
			},
		},
	},
};

local
	// Encoded key for a specific account, belonigng to //Alice
	aliceAccount = sourceChain.System._encodeKey.Account(['0xd43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d']),
	// Encoded key for total issuance
	totalIssuance = sourceChain.Balances._encodeKey.TotalIssuance([]),
	// Single nominal for a 18-decimal token
 	tokenNominal = cql.calc(["10", "18", "**"]),
	// One million tokens
 	million = cql.calc([tokenNominal, "10", "6", "**", "*"]),
;

// Further modify the spec to additionally include Alice's account and totalIssuance, modified by their account's inclusion
outSpec {
	genesis+: {
		raw+: {
			top+: {
				// Amend total issuance to represent the change in Alice's funds.
				// Subtract the amount present in the chain spec (`super`, referring to the existing `top` section)
				// and add the million tokens that they will have instead.
				[totalIssuance]: cql.calc([
					million,
					if std.objectHas(super, totalIssuance) then sourceChain._decode(typeNames.u128, super[totalIssuance]) else '0',
					if std.objectHas(super, aliceAccount) then sourceChain._decode(typeNames.AccountInfo, super[aliceAccount]).data.free else '0',
					// postfix notation
					'-', '+',
				]),
				// Encode Alice's account information
				[aliceAccount]: sourceChain._encode(typeNames.AccountInfo, {
					nonce: 0,
					consumers: 3,
					providers: 1,
					sufficients: 0,
					data: {
						free: million,
						reserved: "0",
						misc_frozen: "0",
						fee_frozen: "0",
					},
				},)
			},
		},
	},
}
