grammar extensibella:toAbella:abstractSyntax;


nonterminal SearchWitness with pp, abella_pp, toAbella<SearchWitness>;

abstract production trueSearchWitness
top::SearchWitness ::=
{
  top.pp = "true";
  top.abella_pp = "true";
}


abstract production applySearchWitness
top::SearchWitness ::= name::String
{
  top.pp = "apply " ++ name;
  top.abella_pp = "apply " ++ name;
}


abstract production leftSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "left (" ++ sub.pp ++ ")";
  top.abella_pp = "left (" ++ sub.abella_pp ++ ")";
}


abstract production rightSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "right (" ++ sub.pp ++ ")";
  top.abella_pp = "right (" ++ sub.abella_pp ++ ")";
}


abstract production splitSearchWitness
top::SearchWitness ::= l::SearchWitness r::SearchWitness
{
  top.pp = "split(" ++l.pp ++ ", " ++ r.pp ++ ")";
  top.abella_pp =
      "split(" ++l.abella_pp ++ ", " ++ r.abella_pp ++ ")";
}


abstract production introsSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "intros [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
  top.abella_pp =
     "intros [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.abella_pp ++ ")";
}


abstract production forallSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "forall [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
  top.abella_pp =
     "forall [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.abella_pp ++ ")";
}


abstract production existsSearchWitness
top::SearchWitness ::= withs::Withs sub::SearchWitness
{
  local withsString::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.pp;
  top.pp = "exists [" ++ withsString ++ "] (" ++ sub.pp ++ ")";
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp = "exists [" ++ withsString_abella ++ "] (" ++
                  sub.abella_pp ++ ")";
}


abstract production unfoldSearchWitness
top::SearchWitness ::= name::String n::Integer swl::[SearchWitness]
{
  local swlString::String =
     if null(swl)
     then ""
     else foldr1(\a::String b::String -> a ++ ", " ++ b,
                 map(\x::SearchWitness -> x.pp, swl));
  top.pp = "unfold(" ++ name ++ ", " ++ toString(n) ++ swlString ++ ")";
  local swlString_abella::String =
     if null(swl)
     then ""
     else foldr1(\a::String b::String -> a ++ ", " ++ b,
                 map(\x::SearchWitness -> x.abella_pp, swl));
  top.abella_pp = "unfold(" ++ name ++ ", " ++ toString(n) ++
                  swlString_abella ++ ")";
}


abstract production starSearchWitness
top::SearchWitness ::=
{
  top.pp = "*";
  top.abella_pp = "*";
}


abstract production eqSearchWitness
top::SearchWitness ::=
{
  top.pp = "=";
  top.abella_pp = "=";
}

