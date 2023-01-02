grammar extensibella:toAbella:abstractSyntax;

--All full QNames, but otherwise the same
synthesized attribute full<a>::a;

attribute
   full<Defs>
occurs on Defs;

aspect production singleDefs
top::Defs ::= d::Def
{
  top.full = singleDefs(d.full);
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.full = consDefs(d.full, rest.full);
}




attribute
   full<Def>
occurs on Def;

aspect production factDef
top::Def ::= clausehead::Metaterm
{
  top.full = factDef(clausehead.full);
}


aspect production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.full = ruleDef(clausehead.full, body.full);
}





attribute
   full<ExtThms>
occurs on ExtThms;

aspect production endExtThms
top::ExtThms ::=
{
  top.full = endExtThms();
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String rest::ExtThms
{
  top.full =
      addExtThms(fullName, bindings, body.full, onLabel, rest.full);
}





attribute
   full<ExtBody>
occurs on ExtBody;

aspect production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.full = endExtBody(conc.full);
}


aspect production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.full = addLabelExtBody(label, m.full, rest.full);
}


aspect production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.full = addBasicExtBody(m.full, rest.full);
}


attribute
   full<Metaterm>
occurs on Metaterm;

aspect production relationMetaterm
top::Metaterm ::= rel::QName args::TermList r::Restriction
{
  top.full = relationMetaterm(rel.fullRel.name, args.full, r);
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.full = top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.full = top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = eqMetaterm(t1.full, t2.full);
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = impliesMetaterm(t1.full, t2.full);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = orMetaterm(t1.full, t2.full);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.full = andMetaterm(t1.full, t2.full);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::Bindings body::Metaterm
{
  top.full = bindingMetaterm(b, bindings.full, body.full);
}


aspect production translationMetaterm
top::Metaterm ::= args::TermList ty::QName orig::Term trans::Term
{
  top.full = translationMetaterm(args.full, ty.fullType.name,
                                 orig.full, trans.full);
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = plusMetaterm(t1.full, t2.full, result.full);
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = minusMetaterm(t1.full, t2.full, result.full);
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = multiplyMetaterm(t1.full, t2.full, result.full);
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = divideMetaterm(t1.full, t2.full, result.full);
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = modulusMetaterm(t1.full, t2.full, result.full);
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.full = negateMetaterm(t.full, result.full);
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = lessMetaterm(t1.full, t2.full);
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = lessEqMetaterm(t1.full, t2.full);
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = greaterMetaterm(t1.full, t2.full);
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.full = greaterEqMetaterm(t1.full, t2.full);
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = appendMetaterm(t1.full, t2.full, result.full);
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = orBoolMetaterm(t1.full, t2.full, result.full);
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.full = andBoolMetaterm(t1.full, t2.full, result.full);
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.full = notBoolMetaterm(t.full, result.full);
}





attribute
   full<Bindings>
occurs on Bindings;

aspect production oneBinding
top::Bindings ::= name::String mty::MaybeType
{
  top.full = oneBinding(name, mty.full);
}


aspect production addBindings
top::Bindings ::= name::String mty::MaybeType rest::Bindings
{
  top.full = addBindings(name, mty.full, rest.full);
}





attribute
   full<Term>
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.full = applicationTerm(f.full, args.full);
}


aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.full =
      if !name.isQualified && contains(name.shortName, top.boundNames)
      then nameTerm(name, mty.full)
      else case name.fullConstr of
           | left(x) -> nameTerm(x.name, mty.full)
           | right(x) -> nameTerm(x.name, mty.full)
           end;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.full = consTerm(t1.full, t2.full);
}


aspect production nilTerm
top::Term ::=
{
  top.full = top;
}


aspect production underscoreTerm
top::Term ::= mty::MaybeType
{
  top.full = top;
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.full = top;
}


aspect production stringTerm
top::Term ::= contents::String
{
  top.full = top;
}


aspect production trueTerm
top::Term ::=
{
  top.full = top;
}


aspect production falseTerm
top::Term ::=
{
  top.full = top;
}


aspect production charTerm
top::Term ::= c::String
{
  top.full = top;
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.full = pairTerm(contents.full);
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.full = listTerm(contents.full);
}





attribute
   full<ListContents>
occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.full = emptyListContents();
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.full = addListContents(hd.full, tl.full);
}





attribute
   full<PairContents>
occurs on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.full = singlePairContents(t.full);
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.full = addPairContents(t.full, rest.full);
}





attribute
   full<TermList>
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.full = singleTermList(t.full);
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.full = consTermList(t.full, rest.full);
}


aspect production emptyTermList
top::TermList ::=
{
  top.full = emptyTermList();
}





attribute
   full<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.full = arrowType(ty1.full, ty2.full);
}


aspect production nameType
top::Type ::= name::QName
{
  top.full = nameType(name.fullType.name);
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.full = functorType(functorTy.full, argTy.full);
}


aspect production underscoreType
top::Type ::=
{
  top.full = underscoreType();
}


attribute
   full<TypeList>
occurs on TypeList;

aspect production emptyTypeList
top::TypeList ::=
{
  top.full = emptyTypeList();
}


aspect production addTypeList
top::TypeList ::= ty::Type rest::TypeList
{
  top.full = addTypeList(ty.full, rest.full);
}


attribute
   full<MaybeType>
occurs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.full = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.full = justType(ty.full);
}
