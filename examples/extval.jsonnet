local chain = cql.fullDump(import "dump.json");
local of(o, n) = if n in o then n;
chain._decodeExtrinsic("0x0103840036c4ad1f01a8479adf6c2dd5acc45cb83dea9a74c8e0e7fa21ffdafa52d1021c014428edf71bee7522c62a6e3f5e58d42abc58ad7e8733ae06c06c6504ce4dd3364ff64570af568f7824e1341cf84bff29b335ae54294f18975689d039dc359f8900ed01000002550131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131313131", function(v)
local runtimeWasm = cql.runtimeWasm(chain._raw[cql.toHex(std.encodeUTF8(':code'))]);
{
	[of(v, 'CheckSpecVersion')]: runtimeWasm.version.spec_version,
	[of(v, 'CheckTxVersion')]: runtimeWasm.version.transaction_version,
	[of(v, 'CheckGenesis')]: chain.System.BlockHash['0'],
	[of(v, 'CheckMortality')]: if v.CheckMortality == 'Immortal' then chain.System.BlockHash['0'] else error 'mortal transactions are not supported',
})
