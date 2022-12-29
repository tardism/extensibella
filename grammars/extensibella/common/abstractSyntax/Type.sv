grammar extensibella:common:abstractSyntax;


nonterminal Type with
   pp, abella_pp, isAtomic,
   toList<Type>, --type broken into a list across arrows
   typeEnv;
propagate typeEnv on Type;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = (if ty1.isAtomic
            then ty1.pp
            else "(" ++ ty1.pp ++ ")") ++ " -> " ++ ty2.pp;
  top.abella_pp = (if ty1.isAtomic
                   then ty1.abella_pp
                   else "(" ++ ty1.abella_pp ++ ")") ++
                  " -> " ++ ty2.abella_pp;
  top.isAtomic = false;

  top.toList = ty1.toList ++ ty2.toList;
}

abstract production nameType
top::Type ::= name::QName
{
  top.pp = name.pp;
  top.abella_pp = name.abella_pp;
  top.isAtomic = true;

  top.toList = [top];
}

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " " ++ if argTy.isAtomic
                                  then argTy.pp
                                  else "(" ++ argTy.pp ++ ")";
  top.abella_pp = functorTy.abella_pp ++ " " ++
                  if argTy.isAtomic
                  then argTy.abella_pp
                  else "(" ++ argTy.abella_pp ++ ")";
  top.isAtomic = false;

  top.toList = [top];
}

abstract production underscoreType
top::Type ::=
{
  top.pp = "_";
  top.abella_pp = "_";
  top.isAtomic = true;

  top.toList = [top];
}





nonterminal TypeList with
   pp, abella_pp,
   toList<Type>, len,
   typeEnv;
propagate typeEnv on TypeList;

abstract production emptyTypeList
top::TypeList ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;
}


abstract production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.pp = if rest.pp == ""
           then ty.pp
           else ty.pp ++ ", " ++ rest.pp;
  top.abella_pp = if rest.abella_pp == ""
                  then ty.abella_pp
                  else ty.abella_pp ++ ", " ++ rest.abella_pp;

  top.toList = ty::rest.toList;
  top.len = 1 + rest.len;
}





nonterminal MaybeType with
   pp, abella_pp,
   typeEnv,
   isJust;
propagate typeEnv on MaybeType;

abstract production nothingType
top::MaybeType ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.isJust = false;
}


abstract production justType
top::MaybeType ::= ty::Type
{
  top.pp = ty.pp;
  top.abella_pp = ty.abella_pp;

  top.isJust = true;
}
