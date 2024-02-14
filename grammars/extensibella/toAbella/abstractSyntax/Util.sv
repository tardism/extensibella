grammar extensibella:toAbella:abstractSyntax;


--This isn't included in Silver's library for some reason
function capitalizeString
String ::= s::String
{
  return
     if s == ""
     then ""
     else case substring(0, 1, s) of
          | "a" -> "A" | "b" -> "B" | "c" -> "C" | "d" -> "D" | "e" -> "E"
          | "f" -> "F" | "g" -> "G" | "h" -> "H" | "i" -> "I" | "j" -> "J"
          | "k" -> "K" | "l" -> "L" | "m" -> "M" | "n" -> "N" | "o" -> "O"
          | "p" -> "P" | "q" -> "Q" | "r" -> "R" | "s" -> "S" | "t" -> "T"
          | "u" -> "U" | "v" -> "V" | "w" -> "W" | "x" -> "X" | "y" -> "Y"
          | "z" -> "Z" |  _  -> substring(0, 1, s)
          end ++ substring(1, length(s), s);
}


--Remove digits from the end of the string
function dropNums
String ::= s::String
{
  return if isDigit(substring(length(s) - 1, length(s), s))
         then dropNums(substring(0, length(s) - 1, s))
         else s;
}


--Split based on actual conjunctions
function splitMetaterm
[Metaterm] ::= mt::Metaterm
{
  return mt.splitConjunctions;
}
--Split based on implies, taking all but conclusion
function metatermPremises
[Metaterm] ::= m::Metaterm
{
  return init(m.splitImplies);
}




--Find the metaterm which is the body of a hypothesis
function get_arg_hyp_metaterm
Maybe<Metaterm> ::= arg::ApplyArg hyps::[(String, Metaterm)]
{
  return
     case arg of
     | hypApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     | starApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     end;
}





--Safely replace a whole list of variables with a list of terms
--that might contain the same variables, but those should stay
function safeReplace
  attribute substName occurs on a,
  attribute substTerm occurs on a,
  attribute subst<a> {substName, substTerm} occurs on a,
  attribute usedNames {} occurs on a =>
[a] ::= replaceIn::[a] replaceVars::[String] replaceTerms::[Term]
{
  local usedNames::[String] =
      replaceVars ++ flatMap((.usedNames), replaceIn) ++
      flatMap((.usedNames), replaceTerms);

  --replace replaceVars with ones fresh in everything for safety in
  --replacing them in the transArgs
  local newVars::[String] =
      foldr(\ x::String rest::[String] ->
              freshName(x, rest ++ usedNames)::rest,
            [], replaceVars);

  --replace replaceVars with newVars in replaceIn
  local step1::[a] =
      map(\ t::a ->
            foldr(\ p::(String, String) rest::a ->
                    decorate rest with {
                      substName=p.1; substTerm=basicNameTerm(p.2);
                    }.subst,
                  t, zip(replaceVars, newVars)),
          replaceIn);

  --replace newVars with the corresponding terms from replaceTerms,
  --now that it is safe to do so
  local step2::[a] =
      map(\ t::a ->
            foldr(\ p::(String, Term) rest::a ->
                    decorate rest with {
                      substName=p.1; substTerm=p.2;
                    }.subst,
                  t, zip(newVars, replaceTerms)),
          step1);

  return step2;
}





function subset
Eq a => Boolean ::= sub::[a] super::[a]
{
  return
     case sub of
     | [] -> true
     | h::t -> contains(h, super) && subset(t, super)
     end;
}


function setEq
Eq a => Boolean ::= l1::[a] l2::[a]
{
  return subset(l1, l2) && subset(l2, l1);
}
