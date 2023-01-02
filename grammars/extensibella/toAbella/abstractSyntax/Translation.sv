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






--Make a name that isn't in usedNames, starting with the given base
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

