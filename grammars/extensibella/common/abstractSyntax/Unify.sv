grammar extensibella:common:abstractSyntax;


{-
  Unify two lists of terms that do not conceptually share any
  variables (i.e. the same variable name might occur in both, but it
  is not meant to refer to the same variable)
-}
function unifyTermsSuccess
Boolean ::= t1::[Term] t2::[Term]
{
  --first, make sure the variables in the two are disjoint
  local t2Names::[String] = flatMap((.usedNames), t2);
  local usedVars::[String] = flatMap((.usedNames), t1) ++ t2Names;
  local newVars::[String] =
      foldr(\ x::String rest::[String] -> freshName(x, rest)::rest,
            [], t2Names);
  local zipped::[(String, Term)] =
      zipWith(\ a::String b::String -> (a, basicNameTerm(b)),
              t2Names, newVars);
  local substed::[Term] =
      map(\ t::Term ->
            foldr(\ p::(String, Term) rest::Term ->
                    decorate rest with {
                       substName = p.1; substTerm = p.2;
                    }.subst,
                  t, zipped),
          t2);
  --unify all the terms in the lists
  return unifyTermsStep(zip(t1, substed));
}


function unifyTermsStep
Boolean ::= eqs::[(Term, Term)]
{
  local tm::Term = head(eqs).1;
  tm.unifyWith = head(eqs).2;

  --substitute all the new substitutions from the current unification
  local substed::[(Term, Term)] =
      map(\ p::(Term, Term) ->
            foldr(\ sub::(String, Term) rest::(Term, Term) ->
                    (decorate rest.1 with {
                        substName = sub.1; substTerm = sub.2;
                     }.subst,
                     decorate rest.2 with {
                        substName = sub.1; substTerm = sub.2;
                     }.subst),
                  p, tm.unifySubst),
          tail(eqs));

  return
      case eqs of
      | [] -> true
      | (a, b)::rest ->
        if !tm.unifySuccess
        then false
        else if !null(tm.unifyEqs)
        then unifyTermsStep(tm.unifyEqs ++ rest)
        else unifyTermsStep(substed)
      end;
}
