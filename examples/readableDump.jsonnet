// Dump chain data in readable format.
//
// Note: Only -concat hashed keys are dumped.
//
// ### Args
// - `chainUrl`: the URL of the chain to pull data from.
//
// ### Usage
// `chainql --tla-str=chainUrl=ws://localhost:9944 readableDump.jsonnet > dump.json`

function(chainUrl)

  local state = cql.chain(chainUrl).latest;
  state._preloadKeys
