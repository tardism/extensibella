grammar extensibella:common:abstractSyntax;


nonterminal Metaterm with
   pp, isAtomic,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv on Metaterm;
propagate boundNames on Metaterm excluding bindingMetaterm;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
  top.isAtomic = true;
}

abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.isAtomic = true;
}

abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.isAtomic = true;
}

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.isAtomic = true;
}

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.isAtomic = false;
}

abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ " \\/ " ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
}

abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ " /\\ " ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
}

abstract production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  top.pp = b.pp ++ " " ++ nameBindings.pp ++ ", " ++ body.pp;
  top.isAtomic = false;

  --Want ALL names which occur, even if only in bindings
  top.usedNames := nameBindings.usedNames ++ body.usedNames;

  body.boundNames = top.boundNames ++ nameBindings.usedNames;
}





nonterminal Bindings with
   pp,
   toList<(String, MaybeType)>, len,
   usedNames,
   typeEnv;
propagate typeEnv on Bindings;

abstract production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.pp =
      if mty.isJust
      then "(" ++ name ++ " : " ++ mty.pp ++ ")"
      else name;

  top.toList = [(name, mty)];
  top.len = 1;

  top.usedNames := [name];
}


abstract production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.pp =
      ( if mty.isJust
        then "(" ++ name ++ " : " ++ mty.pp ++ ")"
        else name ) ++ " " ++ rest.pp;

  top.toList = (name, mty)::rest.toList;
  top.len = 1 + rest.len;

  top.usedNames := name::rest.usedNames;
}




nonterminal Restriction with pp;

abstract production emptyRestriction
top::Restriction ::=
{
  top.pp = "";
}

abstract production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "*");
}

abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "@");
}

abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "+");
}

abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "#");
}




nonterminal Binder with pp;

abstract production forallBinder
top::Binder ::=
{
  top.pp = "forall";
}

abstract production existsBinder
top::Binder ::=
{
  top.pp = "exists";
}

abstract production nablaBinder
top::Binder::=
{
  top.pp = "nabla";
}




nonterminal Term with
   pp, isAtomic,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv on Term;
propagate boundNames on Term;

--Easy equality check
attribute compareTo, isEqual occurs on Type;
propagate compareTo, isEqual on Type;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp =
    ( if f.isAtomic
      then f.pp
      else "(" ++ f.pp ++ ")" ) ++ " " ++ args.pp;
  top.isAtomic = false;
}

abstract production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.pp =
      if mty.isJust
      then "(" ++ name.pp ++ " : " ++ mty.pp ++ ")"
      else name.pp;
  top.isAtomic = true;

  top.usedNames := if name.isQualified then [] else [name.shortName];
}

abstract production consTerm
top::Term ::= t1::Term t2::Term
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ "::" ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
}

abstract production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.isAtomic = true;
}

abstract production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.pp =
      if mty.isJust
      then "(_ : " ++ mty.pp ++ ")"
      else "_";

  top.isAtomic = true;
}




nonterminal TermList with
   pp, toList<Term>,
   typeEnv, constructorEnv, relationEnv,
   usedNames;
propagate typeEnv, constructorEnv, relationEnv on TermList;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";

  top.toList = [t];
}

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;

  top.toList = t::rest.toList;
}

abstract production emptyTermList
top::TermList ::=
{
  top.pp = "";

  top.toList = [];
}

