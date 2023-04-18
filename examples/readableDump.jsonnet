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

  local chain = cql.chain(chainUrl).latest;
  {
    // Iterate over every pallet and every storage in those pallets, and dump the contents into a JSON object
    [palletName]: local pallet = chain[palletName]; {
      [storage]: if std.isObject(pallet[storage]) && std.objectHasEx(pallet[storage], '_preloadKeys', true) then pallet[storage]._preloadKeys else pallet[storage]
      for storage in std.objectFields(pallet)
    }
    for palletName in std.objectFields(chain)
  }
