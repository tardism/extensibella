grammar extensibella:fromAbella:abstractSyntax;


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
top::Metaterm ::= b::Binder nameBindings::[(String, Maybe<Type>)] body::Metaterm
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

