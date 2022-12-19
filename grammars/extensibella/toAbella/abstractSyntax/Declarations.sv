grammar extensibella:toAbella:abstractSyntax;


nonterminal Kind with pp;

abstract production typeKind
top::Kind ::=
{
  top.pp = "type";
}


abstract production arrowKind
top::Kind ::= k::Kind
{
  top.pp = "type -> " ++ k.pp;
}





attribute
   toAbella<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.toAbella = arrowType(ty1.toAbella, ty2.toAbella);
}


aspect production nameType
top::Type ::= name::QName
{
  top.toAbella = nameType(name.fullNT); --need to account for built-in types
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.toAbella = functorType(functorTy.toAbella, argTy.toAbella);
}


aspect production underscoreType
top::Type ::=
{
  top.toAbella = top;
}





nonterminal Defs with pp;

abstract production singleDefs
top::Defs ::= d::Def
{
  top.pp = d.pp;
}


abstract production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.pp = d.pp ++ "; " ++ rest.pp;
}





nonterminal Def with pp;

abstract production factDef
top::Def ::= clausehead::Metaterm
{
  top.pp = clausehead.pp;
}


abstract production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.pp = clausehead.pp ++ " := " ++ body.pp;
}

