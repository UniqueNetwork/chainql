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
local sourceChainState = cql.chain(forkFrom).latest;

// Load the data to encode into the chain spec and filter out the empty entries
local raw = local sourceRaw = sourceChainState._raw._preloadKeys; {
  [key]: cql.toHex(sourceRaw[key])
  for key in std.objectFields(sourceRaw)
  if sourceRaw[key] != null
};

local
auraKeys = [
	// AuraExt.Authorities, we don't have aura pallet enabled for some reason, to refer using cql api
	'0x3c311d57d4daf52904616cf69648081e5e0621c4869aa60c02be9adcc98a0d1d',
	// Aura.Authorities
	'0x57f8dc2f5ab09467896f47300f0424385e0621c4869aa60c02be9adcc98a0d1d',
],

// Keys, the values of which should be taken from the passed spec rather than from the forked chain
wantedKeys = [
	sourceChainState.ParachainInfo._key.ParachainId,
	sourceChainState.Sudo._key.Key,
	sourceChainState.System.BlockHash._key['0'],
	sourceChainState.System._key.ParentHash,
] + auraKeys,

// Keys to remove from the chain spec
unwantedPrefixes = [
	// Aura.CurrentSlot
	'0x57f8dc2f5ab09467896f47300f04243806155b3cd9a8c9e5e9a23fd5dc13a5ed',
	// Ensure there will be no panics caused by unexpected kept state
	sourceChainState.ParachainSystem._key.ValidationData,
	sourceChainState.ParachainSystem._key.RelayStateProof,
	sourceChainState.ParachainSystem._key.HostConfiguration,
	sourceChainState.ParachainSystem._key.LastDmqMqcHead,
	// Part of head
	sourceChainState.System._key.BlockHash,
	sourceChainState.System._key.Number,
	sourceChainState.System._key.Digest,
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

// Take 10 to the power of number `n`
local pow10(n) = std.foldl(function(a, _) a * std.bigint('10'), std.range(0, n), std.bigint('1'));

local
	// Encoded key for a specific account, belonigng to //Alice
	aliceAccount = sourceChainState.System._encodeKey.Account(['0xd43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d']),
	// Encoded key for total issuance
	totalIssuance = sourceChainState.Balances._encodeKey.TotalIssuance([]),
	// One million 18-decimal tokens
	millionTokens = pow10(6 + 18),
;

// Further modify the spec to additionally include Alice's account and totalIssuance, modified by their account's inclusion
outSpec {
	genesis+: {
		raw+: {
			top+: {
				// Amend total issuance to represent the change in Alice's funds.
				// Subtract the amount present in the chain spec (`super`, referring to the existing `top` section)
				// and add the million tokens that they will have instead.
				[totalIssuance]:
					if std.objectHas(super, totalIssuance) then sourceChainState.Balances._decodeValue.TotalIssuance(super[totalIssuance]) else std.bigint(0)
					- if std.objectHas(super, aliceAccount) then sourceChainState.System._decodeValue.Account(super[aliceAccount]).data.free else std.bigint(0)
					+ millionTokens
				,
				// Encode Alice's account information
				[aliceAccount]: sourceChainState.System._encodeValue.Account({
					nonce: 0,
					consumers: 3,
					providers: 1,
					sufficients: 0,
					data: {
						free: millionTokens,
						reserved: std.bigint('0'),
						misc_frozen: std.bigint('0'),
						fee_frozen: std.bigint('0'),
					},
				},)
			},
		},
	},
}
