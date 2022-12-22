grammar extensibella:common:abstractSyntax;


type Env<a> = [a];


--Get all the entries for the name from the environment
function lookupEnv
attribute name {} occurs on a => [a] ::= name::QName env::Env<a>
{
  return
     findAllEnv(
        if name.isQualified
        then \ item::a -> item.name == name
        else \ item::a -> item.name.shortName == name.shortName,
        env);
}


--Why have this?  In case we change the definition of Env
function buildEnv
attribute name {} occurs on a => Env<a> ::= l::[a]
{
  return l;
}


--Find all the items in the Env for which f is true
function findAllEnv
[a] ::= f::(Boolean ::= a) e::Env<a>
{
  return filter(f, e);
}





nonterminal TypeEnvItem with name, transTypes, isLangType;

synthesized attribute isLangType::Boolean;
synthesized attribute transTypes::TypeList;

--types defined in the language encoding
abstract production langTypeEnvItem
top::TypeEnvItem ::= name::QName args::TypeList
{
  top.name = name;

  top.isLangType = true;

  top.transTypes = args;
}


--types defined in the proof files somewhere (current or imported)
abstract production proofTypeEnvItem
top::TypeEnvItem ::= name::QName
{
  top.name = name;

  top.isLangType = false;

  top.transTypes =
      error("Should not access transTypes on proofTypeEnvItem");
}




-- .type is built type
-- .types is arguments
nonterminal ConstructorEnvItem with name, type, types;

abstract production constructorEnvItem
top::ConstructorEnvItem ::= name::QName builtType::Type args::TypeList
{
  top.name = name;

  top.type = builtType;
  top.types = args;
}





nonterminal RelationEnvItem with
   name, types, isExtensible, pcIndex, pcType;

synthesized attribute pcIndex::Integer;
synthesized attribute pcType::Type;

abstract production extRelationEnvItem
top::RelationEnvItem ::= name::QName args::TypeList pcIndex::Integer
{
  top.name = name;

  top.types = args;

  top.isExtensible = true;

  top.pcIndex = pcIndex;
  top.pcType = head(drop(pcIndex, args.toList));
}


abstract production fixedRelationEnvItem
top::RelationEnvItem ::= name::QName args::TypeList
{
  top.name = name;

  top.types = args;

  top.isExtensible = false;

  top.pcIndex = error("Should not access on non-extensible relation");
  top.pcType = error("Should not access on non-extensible relation");
}
