grammar extensibella:common:abstractSyntax;

{-
  This file provides some common functions for name translation and
  checking, such as translating between Abella and user-facing names
  and checking if names have these forms.
-}


--To make a consistent separator for names, I'm going to set it here
global name_sep::String = "-$-";


{-
  When we're translating things, we're going to end up needing the
  names of some constants that will be defined in Abella.  We will
  have those as globals here.
-}

global natSuccName::String = "$succ";
global natZeroName::String = "$zero";

global integerAdditionName::String = "$plus_integer";
global integerSubtractionName::String = "$minus_integer";
global integerMultiplicationName::String = "$multiply_integer";
global integerDivisionName::String = "$divide_integer";
global integerModulusName::String = "$modulus_integer";
global integerNegateName::String = "$negate_integer";
global integerLessName::String = "$less_integer";
global integerLessEqName::String = "$lesseq_integer";
global integerGreaterName::String = "$greater_integer";
global integerGreaterEqName::String = "$greatereq_integer";

global stringType::Type =
       functorType(nameType(toQName("list")),
                   nameType(toQName("$char")));
global is_string::QName = toQName("is_string");

global appendName::String = "$append";

global pairTypeName::String = "$lib__pair";
global pairConstructorName::String = "$pair_c";

global orName::String = "$or_bool";
global andName::String = "$and_bool";
global notName::String = "$not_bool";
global trueName::String = "$btrue";
global falseName::String = "$bfalse";



function transName
QName ::= ty::QName
{
  --need to add "$trans__" to first module portion
  return case ty of
         | basicQName(s) -> transQName(s)
         | _ -> error("Translating types cannot have prefixes")
         end;
}




-- ~99% of the time, this is what we want
function basicNameTerm
Term ::= name::String
{
  return nameTerm(toQName(name), nothingType());
}
