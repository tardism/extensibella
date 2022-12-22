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
   toAbella<Type>, toAbellaMsgs
occurs on Type;
propagate toAbellaMsgs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.toAbella = arrowType(ty1.toAbella, ty2.toAbella);
}


aspect production nameType
top::Type ::= name::QName
{
  --need to account for built-in types
  top.toAbella = nameType(name.fullType.name);
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


attribute
   toAbella<TypeList>, toAbellaMsgs
occurs on TypeList;
propagate toAbellaMsgs on TypeList;

aspect production emptyTypeList
top::TypeList ::=
{
  top.toAbella = emptyTypeList();
}


aspect production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.toAbella = addTypeList(ty.toAbella, rest.toAbella);
}


attribute
   toAbella<MaybeType>, toAbellaMsgs
occurs on MaybeType;
propagate toAbellaMsgs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.toAbella = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.toAbella = justType(ty.toAbella);
}





nonterminal Defs with
   pp,
   toAbella<Defs>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv;

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





nonterminal Def with
   pp,
   toAbella<Def>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv;

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

