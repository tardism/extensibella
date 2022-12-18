grammar extensibella:common:abstractSyntax;

{-
  This file provides some common functions for name translation and
  checking, such as translating between Abella and user-facing names
  and checking if names have these forms.
-}


--To make a consistent separator for names, I'm going to set it here
global name_sep::String = "_$$$$$_";


{-
  When we're translating things, we're going to end up needing the
  names of some constants that will be defined in Abella.  We will
  have those as globals here.
-}

global attributeExistsName::String = "$attr_ex";
global attributeNotExistsName::String = "$attr_no";

global nodeTreeName::String = "$node_tree";
global nodeTreeType::Type = nameType(nodeTreeName);

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
       functorType(nameType("list"), nameType("$char"));

global appendName::String = "$append";

global pairTypeName::String = "$pair";
global pairConstructorName::String = "$pair_c";

global orName::String = "$or_bool";
global andName::String = "$and_bool";
global notName::String = "$not_bool";
global trueName::String = "$btrue";
global falseName::String = "$bfalse";

global isAnythingName::String = "$is_anything";



--Nonterminals
function nameToNonterminalName
String ::= ntName::String
{
  return "$nt_" ++ colonsToEncoded(ntName);
}

function nameToColonNonterminalName
String ::= ntName::String
{
  return "$nt_" ++ encodedToColons(ntName);
}

function nameIsNonterminal
Boolean ::= name::String
{
  return startsWith("$nt_", name);
}

function nonterminalNameToName
String ::= ntName::String
{
  return encodedToColons(substring(4, length(ntName), ntName));
}


--Qualified Names
{-
  We need to encode qualified names with something other than a colon,
  since colons are not allowed in Abella names.  We do this by
  replacing colons with $*$.  This works because we ban dollar signs
  in names otherwise.
-}
function encodedToColons
String ::= s::String
{
  return substitute("$*$", ":", s);
}
function colonsToEncoded
String ::= s::String
{
  return substitute(":", "$*$", s);
}
--Get the grammar and the short name for something
function splitQualifiedName
(String, String) ::= s::String
{
  local ind::Integer = lastIndexOf(":", s);
  return
     if ind < 0
     then error("Not a qualified name to split (" ++ s ++ ")")
     else (substring(0, ind, s), substring(ind + 1, length(s), s));
}
function splitEncodedName
(String, String) ::= s::String
{
  local ind::Integer = lastIndexOf("$*$", s);
  return
     if ind < 0
     then error("Not an encoded name to split (" ++ s ++ ")")
     else (substring(0, ind, s), substring(ind + 3, length(s), s));
}
function isFullyQualifiedName
Boolean ::= s::String
{
  return indexOf(":", s) >= 0;
}

