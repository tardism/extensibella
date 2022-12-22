grammar extensibella:toAbella:abstractSyntax;


attribute
   toAbella<Metaterm>, toAbellaMsgs,
   proverState
occurs on Metaterm;
propagate proverState, toAbellaMsgs on Metaterm;

aspect production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  t.expectRel = true;
  top.toAbella = termMetaterm(t.toAbella, r);
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.toAbella = top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.toAbella = top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  top.toAbella = eqMetaterm(t1.toAbella, t2.toAbella);
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = impliesMetaterm(t1.toAbella, t2.toAbella);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = orMetaterm(t1.toAbella, t2.toAbella);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.toAbella = andMetaterm(t1.toAbella, t2.toAbella);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::Bindings body::Metaterm
{
  top.toAbella = bindingMetaterm(b, bindings.toAbella, body.toAbella);
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerAdditionName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerSubtractionName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerMultiplicationName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerDivisionName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerModulusName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  t.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerNegateName),
            [t.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerLessName),
            [t1.toAbella, t2.toAbella]),
            emptyRestriction());
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerLessEqName),
            [t1.toAbella, t2.toAbella]),
            emptyRestriction());
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerGreaterName),
            [t1.toAbella, t2.toAbella]),
            emptyRestriction());
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(integerGreaterEqName),
            [t1.toAbella, t2.toAbella]),
            emptyRestriction());
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(appendName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(orName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(andName),
            [t1.toAbella, t2.toAbella, result.toAbella]),
            emptyRestriction());
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  t.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(basicNameTerm(notName),
            [t.toAbella, result.toAbella]),
            emptyRestriction());
}





attribute
   toAbella<Bindings>, toAbellaMsgs
occurs on Bindings;
propagate toAbellaMsgs on Bindings;

aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.toAbella = oneBinding(name, mty.toAbella);
}


aspect production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.toAbella = addBindings(name, mty.toAbella, rest.toAbella);
}





attribute
   toAbella<Term>, toAbellaMsgs,
   proverState, expectRel
occurs on Term;
propagate proverState, toAbellaMsgs on Term;
propagate expectRel on Term, TermList, PairContents, ListContents
   excluding applicationTerm;

--whether we expect a term to be a relation or not
inherited attribute expectRel::Boolean;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.toAbella = applicationTerm(f.toAbella, args.toAbella);

  f.expectRel = top.expectRel;
  args.expectRel = false;
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.toAbella =
      if name.isQualified
      then nameTerm(name, mty.toAbella) --assume correctly qualified
      else if contains(name.shortName, top.boundNames)
      then nameTerm(name, mty.toAbella) --assume it refers to the binding
      else if top.expectRel
      then nameTerm(name.fullRel.name, mty.toAbella)
      else --if not expecting a rel and not bound, assume prod
           nameTerm(name.fullConstr.name, mty.toAbella);

  top.toAbellaMsgs <-
      if contains(name.shortName, top.boundNames)
      then []
      else if top.expectRel
      then name.relErrors
      else name.constrErrors;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.toAbella = consTerm(t1.toAbella, t2.toAbella);
}


aspect production nilTerm
top::Term ::=
{
  top.toAbella = top;
}


aspect production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.toAbella = underscoreTerm(mty.toAbella);
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.toAbella = integerToIntegerTerm(i);
}


aspect production stringTerm
top::Term ::= contents::String
{
  local charOrdinals::[Integer] = stringToChars(contents);
  local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  local charTerms::[Term] = map(basicNameTerm(_), charConstants);
  top.toAbella = foldr(consTerm, nilTerm(), charTerms);
}


aspect production trueTerm
top::Term ::=
{
  top.toAbella = basicNameTerm(trueName);
}


aspect production falseTerm
top::Term ::=
{
  top.toAbella = basicNameTerm(falseName);
}


aspect production charTerm
top::Term ::= c::String
{
  top.toAbella = error("Should not have charTerm in toAbella");
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.toAbella = contents.toAbella;
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.toAbella = contents.toAbella;
}





attribute
   toAbella<Term>,
   proverState, expectRel
occurs on ListContents;
propagate proverState on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.toAbella = nilTerm();
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.toAbella = consTerm(hd.toAbella, tl.toAbella);
}





attribute
   toAbella<Term>,
   proverState, expectRel
occurs on PairContents;
propagate proverState on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.toAbella = t.toAbella;
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.toAbella =
      buildApplication(
         basicNameTerm(pairConstructorName),
         [t.toAbella, rest.toAbella]);
}





attribute
   toAbella<TermList>,
   proverState, expectRel
occurs on TermList;
propagate proverState on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.toAbella = singleTermList(t.toAbella);
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.toAbella = consTermList(t.toAbella, rest.toAbella);
}



aspect production emptyTermList
top::TermList ::=
{
  top.toAbella = emptyTermList();
}

