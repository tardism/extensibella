grammar extensibella:toAbella:abstractSyntax;


abstract production computeTactic
top::ProofCommand ::= hyp::String
{
  top.pp = text("compute " ++ hyp ++ ".") ++ line();
  top.abella_pp = justShow(top.pp);

  local state::ProofState = top.proverState.state;
  local maybeHypBody::Maybe<Metaterm> = lookup(hyp, state.hypList);
  local hypBody::Metaterm = maybeHypBody.fromJust;
  hypBody.relationEnv = top.relationEnv;
  hypBody.constructorEnv = top.constructorEnv;
  hypBody.boundNames = state.usedNames;
  hypBody.computeHyp = hyp;

  top.toAbellaMsgs <-
      case maybeHypBody of
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp)]
      | just(_) ->
        if hypBody.isComputable
        then []
        else [errorMsg("Cannot compute " ++ hyp)]
      end;

  top.toAbella = hypBody.computeCmds;
}




synthesized attribute isComputable::Boolean occurs on Metaterm;
inherited attribute computeHyp::String occurs on Metaterm;
synthesized attribute computeCmds::[ProofCommand] occurs on Metaterm;
propagate computeHyp on Metaterm;

aspect default production
top::Metaterm ::=
{
  top.isComputable = false;
  top.computeCmds = error("Should not access computedCmds if not computable");
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant);
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant);
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant);
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      t1.isConstant && t2.isConstant && !result.isConstant;
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      t1.isConstant && t2.isConstant && !result.isConstant;
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.isComputable = (t.isConstant && !result.isConstant) ||
                     (!t.isConstant && result.isConstant);
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term r::Restriction
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant) ||
      --can always compute with nil first
      case t1, t2, result of
      | nilTerm(), _, nameTerm(_, _) -> true
      | nilTerm(), nameTerm(_, _), _ -> true
      | listTerm(emptyListContents()), _, nameTerm(_, _) -> true
      | listTerm(emptyListContents()), nameTerm(_, _), _ -> true
      | stringTerm(""), _, nameTerm(_, _) -> true
      | stringTerm(""), nameTerm(_, _), _ -> true
      | _, _, _ -> false
      end;

  --number of elements in the list we need to go through
  local num::Integer =
      case t1, t2, result of
      --first term known
      | nilTerm(), _, _ -> 0
      | listTerm(c), _, _ -> c.len
      | consTerm(a, b), _, _ -> consLen(t1)
      | stringTerm(s), _, _ -> length(s)
      --result known
      | _, _, nilTerm() -> 0
          --listTerm
      | _, listTerm(ca), listTerm(cr) -> cr.len - ca.len
      | _, consTerm(a, b), listTerm(cr) -> cr.len - consLen(t2)
      | _, nilTerm(), listTerm(cr) -> cr.len
          --consTerm
      | _, listTerm(ca), consTerm(a, b) -> consLen(result) - ca.len
      | _, consTerm(aa, ab), consTerm(ra, rb) ->
        consLen(result) - consLen(t2)
      | _, nilTerm(), consTerm(a, b) -> consLen(result)
          --stringTerm
      | _, stringTerm(sa), stringTerm(sr) -> length(sr) - length(sa)
      --other
      | _, _, _ -> error("Should not access")
      end;
  local consLen::(Integer ::= Term) =
      \ t::Term -> case t of
                   | nilTerm() -> 0
                   | consTerm(_, r) -> 1 + consLen(r)
                   | listTerm(c) -> c.len
                   | _ -> 0
                   end;

  --num + 1 cases
  top.computeCmds =
      foldr(\ i::Integer rest::[ProofCommand] ->
              caseTactic(nameHint("$" ++ toString(i + 1)),
                         "$" ++ toString(i), false)::rest,
            --solved immediately, as this is a hyp
            [assertTactic(nameHint("$0"), nothing(), top)],
            range(0, num));
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant);
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.isComputable =
      (t1.isConstant && t2.isConstant && !result.isConstant) ||
      (t1.isConstant && !t2.isConstant && result.isConstant) ||
      (!t1.isConstant && t2.isConstant && result.isConstant);
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.isComputable = (t.isConstant && !result.isConstant) ||
                     (!t.isConstant && result.isConstant);
}
