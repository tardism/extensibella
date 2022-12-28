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
   pp, abella_pp,
   toAbella<Defs>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs on Defs;

abstract production singleDefs
top::Defs ::= d::Def
{
  top.pp = d.pp;
  top.abella_pp = d.abella_pp;

  top.toAbella = singleDefs(d.toAbella);
}


abstract production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.pp = d.pp ++ "; " ++ rest.pp;
  top.abella_pp = d.abella_pp ++ "; " ++ rest.abella_pp;

  top.toAbella = consDefs(d.toAbella, rest.toAbella);
}





nonterminal Def with
   pp, abella_pp,
   toAbella<Def>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState, currentModule;
propagate typeEnv, constructorEnv, relationEnv, proverState,
          currentModule, toAbellaMsgs on Def;

abstract production factDef
top::Def ::= clausehead::Metaterm
{
  top.pp = clausehead.pp;
  top.abella_pp = clausehead.abella_pp;

  clausehead.boundNames =
      filter(\ s::String -> !isCapitalized(s), clausehead.usedNames);

  top.toAbella = factDef(clausehead.toAbella);
}


abstract production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.pp = clausehead.pp ++ " := " ++ body.pp;
  top.abella_pp = clausehead.abella_pp ++ " := " ++ body.abella_pp;

  local boundNames::[String] =
      filter(\ s::String -> !isCapitalized(s), clausehead.usedNames);
  clausehead.boundNames = boundNames;
  body.boundNames = boundNames;

  top.toAbella = ruleDef(clausehead.toAbella, body.toAbella);
}

