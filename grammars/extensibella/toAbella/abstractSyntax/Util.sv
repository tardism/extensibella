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


--Split based on actual conjunctions
function splitMetaterm
[Metaterm] ::= mt::Metaterm
{
  return mt.splitConjunctions;
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





--Safely replace a whole list of variables with a list of variables
--that might contain the same variables, but those should stay
function safeReplace
[Term] ::= replaceIn::[Term] replaceVars::[String] replaceTerms::[Term]
{
  local usedNames::[String] =
      replaceVars ++ flatMap((.usedNames), replaceIn ++ replaceTerms);

  --replace replaceVars with ones fresh in everything for safety in
  --replacing them in the transArgs
  local newVars::[String] =
      foldr(\ x::String rest::[String] ->
              freshName(x, rest ++ usedNames)::rest,
            [], replaceVars);

  --replace replaceVars with newVars in replaceIn
  local step1::[Term] =
      map(\ t::Term ->
            foldr(\ p::(String, String) rest::Term ->
                    decorate rest with {
                      substName=p.1; substTerm=basicNameTerm(p.2);
                    }.subst,
                  t, zip(replaceVars, newVars)),
          replaceIn);

  --replace newVars with the corresponding terms from replaceTerms,
  --now that it is safe to do so
  local step2::[Term] =
      map(\ t::Term ->
            foldr(\ p::(String, Term) rest::Term ->
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
