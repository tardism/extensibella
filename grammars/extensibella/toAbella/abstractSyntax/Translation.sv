grammar extensibella:toAbella:abstractSyntax;



function ordinalToCharConstructor
String ::= ord::Integer
{
  return "$c_" ++ toString(ord);
}




function integerToIntegerTerm
Term ::= i::Integer
{
  return if i >= 0
         then buildApplication(nameTerm("$posInt", nothing()),
                               [integerToNatTerm(i)])
         else buildApplication(nameTerm("$negSuccInt", nothing()),
                               [integerToNatTerm((i * -1) - 1)]);
}

function integerToNatTerm
Term ::= i::Integer
{
  return if i == 0
         then nameTerm(natZeroName, nothing())
         else buildApplication(nameTerm(natSuccName, nothing()),
                               [integerToNatTerm(i-1)]);
}






function extensible_theorem_name
String ::= name::String grmmr::String
{
  return "$Extensible_Theorem_" ++ colonsToEncoded(name) ++
         name_sep ++ colonsToEncoded(grmmr);
}


--Make a name that isn't in usedNames, based on the type
function makeUniqueNameFromTy
String ::= ty::Type usedNames::[String]
{
  local base::String =
        if true --tyIsNonterminal(ty)
        then let qualName::String =
                 substring(3, length([1]), --length(ty.headTypeName.fromJust),
                           error("makeUniqueNameFromTy (extensibella:toAbella:abstractSyntax:Translation.sv)")) --ty.headTypeName.fromJust)
             in
               if isFullyQualifiedName(qualName)
               then substring(0, 1, splitQualifiedName(qualName).2)
               else substring(0, 1, qualName)
             end
        else case error("makeUniqueNameFromTy (extensibella:toAbella:abstractSyntax:Translation.sv)") of --ty.headTypeName of
             | nothing() -> "A"
             | just("integer") -> "N"
             | just(str) ->
               if isAlpha(substring(0, 1, str))
               then --capitalize the first character
                    charsToString([head(stringToChars(substring(0, 1, str))) - 32])
               else substring(0, 1, str)
             end;
  return
     if contains(base, usedNames)
     then makeUniqueName(base, 1, usedNames)
     else base;
}


--Make anem that isn't in usedNames, starting with the given base
function makeUniqueNameFromBase
String ::= base::String usedNames::[String]
{
  return
     if contains(base, usedNames)
     then makeUniqueName(base, 1, usedNames)
     else base;
}


--Make a name starting with base that isn't in usedNames
function makeUniqueName
String ::= base::String index::Integer usedNames::[String]
{
  return
     if contains(base ++ toString(index), usedNames)
     then makeUniqueName(base, index + 1, usedNames)
     else base ++ toString(index);
}

