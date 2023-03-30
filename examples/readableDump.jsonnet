// Dump chain data in readable format
//
// Only -concat hashed keys are dumped
//
// Usage: chainql --tla-str=chainUrl=ws://my-chain:9944 readableDump.jsonnet > dump.json

function(chainUrl)

  local quartz = cql.chain(chainUrl).latest;
  {
    [palletName]: local pallet = quartz[palletName]; {
      [storage]: if std.isObject(pallet[storage]) && std.objectHasEx(pallet[storage], '_preloadKeys', true) then pallet[storage]._preloadKeys else pallet[storage]
      for storage in std.objectFields(pallet)
    }
    for palletName in std.objectFields(quartz)
  }
