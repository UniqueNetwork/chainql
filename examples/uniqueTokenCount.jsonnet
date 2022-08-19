function(chainUrl)

local quartz = cql.chain(chainUrl).latest;

local
	collections = quartz.Common.CollectionById._preloadKeys,
	collectionsByType(type) = std.filter(function(c) c.mode == type || std.isObject(c.mode) && std.objectHas(c.mode, type), std.objectValues(collections)),
;

local data = {
	nft: {
		minted: std.foldr(function(a, b) a + b, std.objectValues(quartz.Nonfungible.TokensMinted._preloadKeys), 0),
		burnt: std.foldr(function(a, b) a + b, std.objectValues(quartz.Nonfungible.TokensBurnt._preloadKeys), 0),
		alive: self.minted - self.burnt,
		_collections:: collectionsByType('NFT'),
		collectionCount: std.length(self._collections),
	},
	refungible: {
		minted: std.foldr(function(a, b) a + b, std.objectValues(quartz.Refungible.TokensMinted._preloadKeys), 0),
		burnt: std.foldr(function(a, b) a + b, std.objectValues(quartz.Refungible.TokensBurnt._preloadKeys), 0),
		alive: self.minted - self.burnt,
		_collections:: collectionsByType('ReFungible'),
		collectionCount: std.length(self._collections),
	},
	fungible: {
		_collections:: collectionsByType('Fungible'),
		collectionCount: std.length(self._collections),
	},
};

std.join('\n', [
	'# HELP tokens_total The total number of existing tokens',
	'# TYPE tokens_total counter',
	'tokens_total{type="NFT"} ' + data.nft.alive,
	'tokens_total{type="ReFungible"} ' + data.refungible.alive,
	'',
	'# HELP collections_total The total number of existing collections',
	'# TYPE collections_total counter',
	'collections_total{type="Fungible"} ' + data.fungible.collectionCount,
	'collections_total{type="NFT"} ' + data.nft.collectionCount,
	'collections_total{type="Refungible"} ' + data.refungible.collectionCount,
])
