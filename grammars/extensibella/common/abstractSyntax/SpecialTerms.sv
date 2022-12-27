grammar extensibella:common:abstractSyntax;


--METATERMS
abstract production translationMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term trans::Term
{
  top.pp = (if args.len == 0 then "" else args.pp ++ " ") ++
           "|{" ++ ty.pp ++ "}- " ++ orig.pp ++ " ~~> " ++ trans.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}


{-
  Why don't we just put these operations in Term?  Then we could use
  something like `3+4` directly in the next addition.  That sounds
  wonderful, but it doesn't really fit the Abella style, and thus it
  would be really difficult to use.  We would not have a good way to
  use properties of the arithmetic operations, which are properties
  that need to be applied.

  The translation of the numeric operations will need to be dependent
  on typing once we add floats.
-}
abstract production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " + " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " - " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " * " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " / " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " mod " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "- " ++ t.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " < " ++ t2.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " <= " ++ t2.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " > " ++ t2.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " >= " ++ t2.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " ++ " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " || " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " && " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "! " ++ t.pp ++ " = " ++ result.pp;
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}





--TERMS
abstract production intTerm
top::Term ::= i::Integer
{
  top.pp = toString(i);
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production stringTerm
top::Term ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production pairTerm
top::Term ::= contents::PairContents
{
  top.pp = "(" ++ contents.pp ++ ")";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}

abstract production charTerm
top::Term ::= char::String
{
  top.pp = "\"" ++ char ++ "\"";
  top.abella_pp = error("Should not access abella_pp");
  top.isAtomic = true;
}




nonterminal ListContents with
   pp,
   toList<Term>,
   typeEnv, constructorEnv, relationEnv,
   usedNames;
propagate typeEnv, constructorEnv, relationEnv on ListContents;

abstract production emptyListContents
top::ListContents ::=
{
  top.pp = "";
  top.toList = [];
}

abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
  top.toList = t::rest.toList;
}




nonterminal PairContents with
   pp,
   toList<Term>,
   typeEnv, constructorEnv, relationEnv,
   usedNames;
propagate typeEnv, constructorEnv, relationEnv on PairContents;

abstract production singlePairContents
top::PairContents ::= t::Term
{
  top.pp = t.pp;
  top.toList = [t];
}

abstract production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.pp = t.pp ++ ", " ++ rest.pp;
  top.toList = t::rest.toList;
}

