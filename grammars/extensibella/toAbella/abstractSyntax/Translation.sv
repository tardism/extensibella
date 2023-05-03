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


--Name of accumulator relation for strong induction on ints
global intStrongInductionRel::QName = toQName("acc");
