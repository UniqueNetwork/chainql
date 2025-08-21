local state = cql.chain('wss://rpc.unique.network').latest;

{
key: state.Aura._key.Authorities,
currentList: state.Aura.Authorities,
currentValue: state.Aura._encodeValue.Authorities($.currentList),
wantedList: state.Aura.Authorities + [/*Сюда список новых авторити, e.g*/ cql.ss58('5Da8qREfhvAkkmkBHjJM44amdfMZV2hBrYTEdGPdLYXLEw1j')],
wantedValue: state.Aura._encodeValue.Authorities($.wantedList),
}
