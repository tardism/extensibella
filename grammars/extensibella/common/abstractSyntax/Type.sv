grammar extensibella:common:abstractSyntax;


nonterminal Type with
   pp, isAtomic,
   typeEnv;
propagate typeEnv on Type;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = (if ty1.isAtomic
            then ty1.pp
            else "(" ++ ty1.pp ++ ")") ++ " -> " ++ ty2.pp;
  top.isAtomic = false;
}

abstract production nameType
top::Type ::= name::QName
{
  top.pp = name.pp;
  top.isAtomic = true;
}

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " " ++ if argTy.isAtomic
                                  then argTy.pp
                                  else "(" ++ argTy.pp ++ ")";
  top.isAtomic = false;
}

abstract production underscoreType
top::Type ::=
{
  top.pp = "_";
  top.isAtomic = true;
}





nonterminal TypeList with
   pp,
   toList<Type>, len,
   typeEnv;
propagate typeEnv on TypeList;

abstract production emptyTypeList
top::TypeList ::=
{
  top.pp = "";

  top.toList = [];
  top.len = 0;
}


abstract production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.pp = if rest.pp == ""
           then ty.pp
           else ty.pp ++ ", " ++ rest.pp;

  top.toList = ty::rest.toList;
  top.len = 1 + rest.len;
}





nonterminal MaybeType with
   pp,
   typeEnv,
   isJust;
propagate typeEnv on MaybeType;

abstract production nothingType
top::MaybeType ::=
{
  top.pp = "";

  top.isJust = false;
}


abstract production justType
top::MaybeType ::= ty::Type
{
  top.pp = ty.pp;

  top.isJust = true;
}
