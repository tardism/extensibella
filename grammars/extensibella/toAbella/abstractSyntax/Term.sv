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
top::Metaterm ::= b::Binder bindings::[(String, Maybe<Type>)] body::Metaterm
{
  --Map toAbella over the bindings for the types
  --(to-ed bindings, as in "to" has been done to them)
  local toedBindings::[(String, Maybe<Type>)] =
        map(\ p::(String, Maybe<Type>) ->
              (p.1, case p.2 of
                    | nothing() -> nothing()
                    | just(ty) ->
                      just(decorate ty with {
                              languageCtx = top.languageCtx;
                           }.toAbella)
                    end),
            bindings);
  top.toAbella = bindingMetaterm(b, toedBindings, body.toAbella);
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  t1.expectRel = false;
  t2.expectRel = false;
  result.expectRel = false;
  top.toAbella =
      termMetaterm(
         buildApplication(nameTerm(baseName(integerAdditionName), nothing()),
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
         buildApplication(nameTerm(baseName(integerSubtractionName), nothing()),
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
         buildApplication(nameTerm(baseName(integerMultiplicationName), nothing()),
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
         buildApplication(nameTerm(baseName(integerDivisionName), nothing()),
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
         buildApplication(nameTerm(baseName(integerModulusName), nothing()),
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
         buildApplication(nameTerm(baseName(integerNegateName), nothing()),
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
         buildApplication(nameTerm(baseName(integerLessName), nothing()),
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
         buildApplication(nameTerm(baseName(integerLessEqName), nothing()),
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
         buildApplication(nameTerm(baseName(integerGreaterName), nothing()),
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
         buildApplication(nameTerm(baseName(integerGreaterEqName), nothing()),
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
         buildApplication(nameTerm(baseName(appendName), nothing()),
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
         buildApplication(nameTerm(baseName(orName), nothing()),
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
         buildApplication(nameTerm(baseName(andName), nothing()),
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
         buildApplication(nameTerm(baseName(notName), nothing()),
            [t.toAbella, result.toAbella]),
            emptyRestriction());
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
top::Term ::= name::QName ty::Maybe<Type>
{
  local transTy::Maybe<Type> =
        case ty of
        | nothing() -> nothing()
        | just(t) -> just(decorate t with {
                             languageCtx = top.languageCtx;
                          }.toAbella)
        end;
  top.toAbella =
      if name.isQualified
      then nameTerm(name, transTy) --assume correctly qualified
      else if contains(name.shortName, top.boundNames)
      then nameTerm(name, transTy) --assume it refers to the binding
      else if top.expectRel
      then nameTerm(name.fullRel, transTy)
      else --if not expecting a rel and not bound, assume prod
           nameTerm(name.fullProd, transTy);

  top.toAbellaMsgs <-
      if contains(name.shortName, top.boundNames)
      then []
      else if top.expectRel
      then name.relErrors
      else name.prodErrors;
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
top::Term ::= ty::Maybe<Type>
{
  local transTy::Maybe<Type> =
        case ty of
        | nothing() -> nothing()
        | just(t) -> just(decorate t with {
                             languageCtx = top.languageCtx;
                          }.toAbella)
        end;
  top.toAbella = underscoreTerm(transTy);
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
  local charQs::[QName] = map(baseName, charConstants);
  local charTerms::[Term] = map(nameTerm(_, nothing()), charQs);
  top.toAbella = foldr(consTerm, nilTerm(), charTerms);
}


aspect production trueTerm
top::Term ::=
{
  top.toAbella = nameTerm(baseName(trueName), nothing());
}


aspect production falseTerm
top::Term ::=
{
  top.toAbella = nameTerm(baseName(falseName), nothing());
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
         nameTerm(baseName(pairConstructorName), nothing()),
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

