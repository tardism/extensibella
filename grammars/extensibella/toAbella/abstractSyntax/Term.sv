grammar extensibella:toAbella:abstractSyntax;


--attribute occurs on Metaterm;


aspect production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{

}


aspect production trueMetaterm
top::Metaterm ::=
{

}


aspect production falseMetaterm
top::Metaterm ::=
{

}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{

}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{

}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{

}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{

}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[(String, Maybe<Type>)] body::Metaterm
{

}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{

}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{

}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{

}





--attribute occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{

}


aspect production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{

}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{

}


aspect production nilTerm
top::Term ::=
{

}


aspect production underscoreTerm
top::Term ::= ty::Maybe<Type>
{

}


aspect production intTerm
top::Term ::= i::Integer
{

}


aspect production stringTerm
top::Term ::= contents::String
{
  --local charOrdinals::[Integer] = stringToChars(contents);
  --local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  --local charTerms::[Term] = map(nameTerm(_, nothing()), charConstants);
  --top.translation = foldr(consTerm, nilTerm(), charTerms);
}


aspect production trueTerm
top::Term ::=
{

}


aspect production falseTerm
top::Term ::=
{

}


aspect production charTerm
top::Term ::= c::String
{

}


aspect production pairTerm
top::Term ::= contents::PairContents
{

}


aspect production listTerm
top::Term ::= contents::ListContents
{

}





--attribute occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{

}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{

}





--attribute occurs on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{

}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{

}





--attribute occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{

}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{

}



aspect production emptyTermList
top::TermList ::=
{

}

