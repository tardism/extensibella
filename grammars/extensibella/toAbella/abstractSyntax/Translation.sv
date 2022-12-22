grammar extensibella:toAbella:abstractSyntax;



function ordinalToCharConstructor
String ::= ord::Integer
{
  return "$c_" ++ toString(ord);
}




function integerToIntegerTerm
Term ::= i::Integer
{
  return
     if i >= 0
     then buildApplication(basicNameTerm("$posInt"),
                           [integerToNatTerm(i)])
     else buildApplication(basicNameTerm("$negSuccInt"),
                           [integerToNatTerm((i * -1) - 1)]);
}

function integerToNatTerm
Term ::= i::Integer
{
  return
     if i == 0
     then basicNameTerm(natZeroName)
     else buildApplication(basicNameTerm(natSuccName),
                           [integerToNatTerm(i-1)]);
}






--Make a name that isn't in usedNames, based on the type
function makeUniqueNameFromTy
String ::= ty::Type usedNames::[String]
{
  local base::String =
        case error("makeUniqueNameFromTy (extensibella:toAbella:abstractSyntax:Translation.sv)") of --ty.headTypeName of
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

