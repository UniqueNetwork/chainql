// UTILITY FOR OTHER EXAMPLES.
// Categorize the types used on the chain for the purposes such as decoding.
//
// ### Args
// - `chain`: Chain information as a Jsonnet object.

function(chain)
local
	typeName(id) = local
		ty = chain._meta.types.types[id],
		name = if std.objectHas(ty.type, "path") then
			std.join('::', ty.type.path)
		else if std.objectHas(ty.type.def, "primitive") then ty.type.def.primitive
		else if std.objectHas(ty.type.def, "tuple") then "(" + std.join(', ', std.map(typeName, ty.type.def.tuple)) + ")"
		else if std.objectHas(ty.type.def, "sequence") then "Vec<" + typeName(ty.type.def.sequence.type) + ">"
		else if std.objectHas(ty.type.def, "array") then "[" + typeName(ty.type.def.array.type) + "; " + ty.type.def.array.len + "]"
		else if std.objectHas(ty.type.def, "compact") then "Compact<" + typeName(ty.type.def.compact.type) + ">"
		else error "Can't generate useable name for " + ty.type,
		generics = if std.objectHas(ty.type, "params") then
			'<' + std.join(', ', std.map(function(p) if p.type == null then 'Spec#'+id else typeName(p.type), ty.type.params)) + '>'
		else ''
	; name + generics,
	shortenPrefix(obj, prefix, short) = {
		[short]: obj[field]
		for field in std.objectFields(obj)
		// There should be at most one element with this prefix
		if std.startsWith(field, prefix)
	},
;

local typesRaw = {
	[typeName(id)]: id
	for id in std.range(0, std.length(chain._meta.types.types)-1)
};

local types = typesRaw + shortenPrefix(typesRaw, 'frame_system::AccountInfo<', 'AccountInfo');

types
