function(chainUrl)

// To ensure there is no hidden fields and unsupported datatypes, there is no tricks
local roundtripJson(obj) = std.parseJson(std.manifestJson(obj));

local state = cql.chain(chainUrl).latest._preloadKeys;

local
	raw = state._raw,
	roundtripRaw = std.trace(roundtripJson(raw)),
;

local 
	decoded = cql.fullDump(roundtripRaw),
	roundtripDecoded = std.trace(roundtripJson(decoded)),
	roundtripMeta = std.trace(roundtripJson(decoded._meta)),
;

local rebuilt = cql.dump(roundtripMeta, {})._rebuild(roundtripDecoded);

assert std.objectFields(rebuilt) == std.objectFields(raw);
std.all([
	if rebuilt[key] != raw[key] then error 'value mismatch for "%s": %s != %s' % [key, rebuilt[key], raw[key]] else true,
	for key in std.objectFields(rebuilt)
])
