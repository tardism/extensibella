grammar extensibella:common:abstractSyntax;


nonterminal Metaterm with
   pp, abella_pp, isAtomic,
   splitImplies, splitConjunctions,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv on Metaterm;
propagate boundNames on Metaterm excluding bindingMetaterm;

abstract production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = rel.pp ++ " " ++ args.pp ++ r.pp;
  top.abella_pp = rel.abella_pp ++ " " ++ args.abella_pp ++ r.pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.abella_pp = "true";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.abella_pp = "false";
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.abella_pp = t1.abella_pp ++ " = " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.abella_pp =
      (if t1.isAtomic
       then t1.abella_pp
       else "(" ++ t1.abella_pp ++ ")") ++ " -> " ++ t2.abella_pp;
  top.isAtomic = false;

  top.splitImplies = t1::t2.splitImplies;
  top.splitConjunctions = [top];
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
  top.abella_pp =
    ( if t1.isAtomic
      then t1.abella_pp
      else "(" ++ t1.abella_pp ++ ")" ) ++ " \\/ " ++
    ( if t2.isAtomic
      then t2.abella_pp
      else "(" ++ t2.abella_pp ++ ")" );
  top.isAtomic = false;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
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
  top.abella_pp =
    ( if t1.isAtomic
      then t1.abella_pp
      else "(" ++ t1.abella_pp ++ ")" ) ++ " /\\ " ++
    ( if t2.isAtomic
      then t2.abella_pp
      else "(" ++ t2.abella_pp ++ ")" );
  top.isAtomic = false;

  top.splitImplies = [top];
  --split both because associative
  top.splitConjunctions = t1.splitConjunctions ++ t2.splitConjunctions;
}

abstract production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::Bindings body::Metaterm
{
  top.pp = b.pp ++ " " ++ nameBindings.pp ++ ", " ++ body.pp;
  top.abella_pp = b.pp ++ " " ++ nameBindings.abella_pp ++ ", " ++
                  body.abella_pp;
  top.isAtomic = false;

  top.splitImplies = body.splitImplies;
  top.splitConjunctions = [top];

  --Want ALL names which occur, even if only in bindings
  top.usedNames := nameBindings.usedNames ++ body.usedNames;

  body.boundNames = top.boundNames ++ nameBindings.usedNames;
}





nonterminal Bindings with
   pp, abella_pp,
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
  top.abella_pp =
      if mty.isJust
      then "(" ++ name ++ " : " ++ mty.abella_pp ++ ")"
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
  top.abella_pp =
      ( if mty.isJust
        then "(" ++ name ++ " : " ++ mty.abella_pp ++ ")"
        else name ) ++ " " ++ rest.abella_pp;

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
   pp, abella_pp, isAtomic,
   typeEnv, constructorEnv, relationEnv,
   isStructured, headConstructor,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv, boundNames on Term;

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
  top.abella_pp =
    ( if f.isAtomic
      then f.abella_pp
      else "(" ++ f.abella_pp ++ ")" ) ++ " " ++ args.abella_pp;
  top.isAtomic = false;

  top.isStructured = true;

  top.headConstructor = f.headConstructor;
}

abstract production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.pp =
      if mty.isJust
      then "(" ++ name.pp ++ " : " ++ mty.pp ++ ")"
      else name.pp;
  top.abella_pp =
      if mty.isJust
      then "(" ++ name.abella_pp ++ " : " ++ mty.abella_pp ++ ")"
      else name.abella_pp;
  top.isAtomic = true;

  top.usedNames := if name.isQualified then [] else [name.shortName];

  top.isStructured = name.constrFound;

  top.headConstructor = name;
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
  top.abella_pp =
    ( if t1.isAtomic
      then t1.abella_pp
      else "(" ++ t1.abella_pp ++ ")" ) ++ "::" ++
    ( if t2.isAtomic
      then t2.abella_pp
      else "(" ++ t2.abella_pp ++ ")" );
  top.isAtomic = false;

  top.isStructured = true;

  top.headConstructor = error("consTerm.headConstructor not valid");
}

abstract production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.abella_pp = "nil";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("nilTerm.headConstructor not valid");
}

abstract production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.pp =
      if mty.isJust
      then "(_ : " ++ mty.pp ++ ")"
      else "_";
  top.abella_pp =
      if mty.isJust
      then "(_ : " ++ mty.abella_pp ++ ")"
      else "_";

  top.isAtomic = true;

  top.isStructured = false;

  top.headConstructor =
      error("underscoreTerm.headConstructor not valid");
}




nonterminal TermList with
   pp, abella_pp, toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames,
   isStructuredList;
propagate typeEnv, constructorEnv, relationEnv, boundNames
   on TermList;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";
  top.abella_pp = if t.isAtomic then t.abella_pp
                                else "(" ++ t.abella_pp ++ ")";

  top.toList = [t];
  top.len = 1;

  top.isStructuredList = [t.isStructured];
}

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;
  top.abella_pp = (if t.isAtomic then t.abella_pp
                                 else "(" ++ t.abella_pp ++ ")") ++
                  " " ++ rest.abella_pp;

  top.toList = t::rest.toList;
  top.len = 1 + rest.len;

  top.isStructuredList = t.isStructured::rest.isStructuredList;
}

abstract production emptyTermList
top::TermList ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.isStructuredList = [];
}

