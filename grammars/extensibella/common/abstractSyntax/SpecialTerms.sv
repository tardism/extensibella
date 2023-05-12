grammar extensibella:common:abstractSyntax;


--METATERMS
abstract production translationMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term trans::Term
{
  top.pp = (if args.len == 0 then "" else args.pp ++ " ") ++
           "|{" ++ ty.pp ++ "}- " ++ orig.pp ++ " ~~> " ++ trans.pp;
  top.abella_pp =
      (if args.len == 0 then "" else args.abella_pp ++ " ") ++
      "|{" ++ ty.pp ++ "}- " ++ orig.abella_pp ++ " ~~> " ++ trans.pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
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
  top.abella_pp = t1.abella_pp ++ " + " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " - " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " - " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " * " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " * " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " / " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " / " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " mod " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " mod " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "- " ++ t.pp ++ " = " ++ result.pp;
  top.abella_pp = "- " ++ t.abella_pp ++ " = " ++ result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " < " ++ t2.pp;
  top.abella_pp = t1.abella_pp ++ " < " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " <= " ++ t2.pp;
  top.abella_pp = t1.abella_pp ++ " <= " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " > " ++ t2.pp;
  top.abella_pp = t1.abella_pp ++ " > " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " >= " ++ t2.pp;
  top.abella_pp = t1.abella_pp ++ " >= " ++ t2.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

--because we can do induction on append, should have a restriction
abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.pp = t1.pp ++ " ++ " ++ t2.pp ++ " = " ++ result.pp ++ r.pp;
  top.abella_pp = t1.abella_pp ++ " ++ " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp ++ r.pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " || " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " || " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " && " ++ t2.pp ++ " = " ++ result.pp;
  top.abella_pp = t1.abella_pp ++ " && " ++ t2.abella_pp ++ " = " ++
                  result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "! " ++ t.pp ++ " = " ++ result.pp;
  top.abella_pp = "! " ++ t.abella_pp ++ " = " ++ result.abella_pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}


--Special relation applications for extSize and transRel
abstract production extSizeMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = "<" ++ rel.pp ++ " {ES}> " ++ args.pp ++ r.pp;
  top.abella_pp =
      "<" ++ rel.abella_pp ++ " {ES}> " ++ args.abella_pp ++ r.pp;
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}

abstract production transRelMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.pp = "<" ++ rel.pp ++ " {T}> " ++ args.pp ++ r.pp;
  top.abella_pp = "<" ++ rel.abella_pp ++ " {T}> " ++
                  args.abella_pp ++ r.pp; 
  top.isAtomic = true;

  top.splitImplies = [top];
  top.splitConjunctions = [top];
}





--TERMS
abstract production unknownTerm
top::Term ::= ty::QName
{
  top.pp = "<unknown " ++ ty.pp ++ ">";
  top.abella_pp = "<unknown " ++ ty.abella_pp ++ ">";
  top.isAtomic = true;

  top.isStructured = true;
  top.isUnknownTerm = true;

  top.headConstructor =
      error("unknownTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | unknownTerm(ty2) -> ty == ty2
      | nameTerm(q, _) when !q.isQualified -> true
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production intTerm
top::Term ::= i::Integer
{
  top.pp = toString(i);
  top.abella_pp = toString(i);
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("intTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | intTerm(j) -> i == j
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production stringTerm
top::Term ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";
  top.abella_pp = "\"" ++ contents ++ "\"";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("stringTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | stringTerm(s) -> contents == s
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.abella_pp = "true";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("trueTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | trueTerm() -> true
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.abella_pp = "false";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("falseTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | falseTerm() -> true
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.abella_pp = "[" ++ contents.abella_pp ++ "]";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("listTerm.headConstructor not valid");

  top.subst = listTerm(contents.subst);

  top.unifySuccess =
      case top.unifyWith of
      | listTerm(c) -> contents.len == c.len
      | consTerm(_, _) -> contents.len > 0
      | nilTerm() -> contents.len == 0
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | listTerm(c) -> zipWith(pair, contents.toList, c.toList)
      | consTerm(a, b) ->
        [(head(contents.toList), a),
         (foldr(consTerm, nilTerm(), tail(contents.toList)), b)]
      | _ -> []
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production pairTerm
top::Term ::= contents::PairContents
{
  top.pp = "(" ++ contents.pp ++ ")";
  top.abella_pp = "(" ++ contents.abella_pp ++ ")";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("pairTerm.headConstructor not valid");

  top.subst = pairTerm(contents.subst);

  top.unifySuccess =
      case top.unifyWith of
      | pairTerm(c) -> contents.len == c.len
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs =
      case top.unifyWith of
      | pairTerm(c) ->
        zipWith(pair, contents.toList, c.toList)
      | _ -> []
      end;
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}

abstract production charTerm
top::Term ::= char::String
{
  top.pp = "\"" ++ char ++ "\"";
  top.abella_pp = "\"" ++ char ++ "\"";
  top.isAtomic = true;

  top.isStructured = true;

  top.headConstructor = error("charTerm.headConstructor not valid");

  top.subst = top;

  top.unifySuccess =
      case top.unifyWith of
      | charTerm(c) -> char == c
      | nameTerm(q, _) -> !q.isQualified
      | _ -> false
      end;
  top.unifyEqs = [];
  top.unifySubst =
      case top.unifyWith of
      | nameTerm(q, _) -> [(q.shortName, top)]
      | _ -> []
      end;
}




nonterminal ListContents with
   pp, abella_pp,
   toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   substName, substTerm, subst<ListContents>,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm on ListContents;

abstract production emptyListContents
top::ListContents ::=
{
  top.pp = "";
  top.abella_pp = "";
  top.toList = [];
  top.len = 0;
  top.subst = top;
}

abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
  top.abella_pp = t.abella_pp ++ (if rest.abella_pp == "" then ""
                                  else ", " ++ rest.abella_pp);
  top.toList = t::rest.toList;
  top.len = 1 + rest.len;
  top.subst = addListContents(t.subst, rest.subst);
}




nonterminal PairContents with
   pp, abella_pp,
   toList<Term>, len,
   typeEnv, constructorEnv, relationEnv,
   substName, substTerm, subst<PairContents>,
   boundNames, usedNames;
propagate typeEnv, constructorEnv, relationEnv, boundNames,
          substName, substTerm on PairContents;

abstract production singlePairContents
top::PairContents ::= t::Term
{
  top.pp = t.pp;
  top.abella_pp = t.abella_pp;
  top.toList = [t];
  top.len = 1;
  top.subst = singlePairContents(t.subst);
}

abstract production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.pp = t.pp ++ ", " ++ rest.pp;
  top.abella_pp = t.abella_pp ++ ", " ++ rest.abella_pp;
  top.toList = t::rest.toList;
  top.len = 1 + rest.len;
  top.subst = addPairContents(t.subst, rest.subst);
}

