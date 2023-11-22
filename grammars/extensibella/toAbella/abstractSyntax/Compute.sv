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
        else [errorMsg("Cannot compute " ++ hyp ++ " (" ++ justShow(hypBody.pp) ++ ")")]
      end;
  {-

    The problem here is that we are getting the Abella version of the
    state, and therefore the hypothesis, rather than the Extensibella
    version.  This is less than useful in this case, and I am
    wondering if it is also a bad thing overall.  How much would it
    break if I changed it to be the Extensibella version of the state
    and hypothesis instead?  That seems more useful in general for
    computation within Extensibella.

  -}

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
      case t1, t2, result of
      --can always compute with full list first and a name to set
      | _, _, nameTerm(_, _) -> fullList(t1)
      | _, nameTerm(_, _), _ -> fullList(t1)
      --only completely-known strings
      | stringTerm(""), _, nameTerm(_, _) -> true
      | stringTerm(""), nameTerm(_, _), _ -> true
      | stringTerm(_), stringTerm(_), nameTerm(_, _) -> true
      | stringTerm(_), nameTerm(_, _), stringTerm(_) -> true
      --nothing else
      | _, _, _ -> unsafeTracePrint(false, "Cannot do " ++ justShow(t1.pp) ++ " (1)\n")
      end;
  local fullList::(Boolean ::= Term) =
      \ t::Term -> case t of
                   | nilTerm() -> true
                   | consTerm(_, r) -> fullList(r)
                   | listTerm(_) -> true
                   | _ -> unsafeTracePrint(false, "Cannot do " ++ justShow(t1.pp) ++ " (2)\n")
                   end;

  --number of elements in the list we need to go through
  local num::Integer = listLen(t1);
  local listLen::(Integer ::= Term) =
      \ t::Term -> case t of
                   | nilTerm() -> 0
                   | consTerm(_, r) -> 1 + listLen(r)
                   | listTerm(c) -> c.len
                   | _ -> 0
                   end;

  --num + 1 cases
  top.computeCmds =
      foldl(\ rest::[ProofCommand] i::Integer ->
              rest ++
              [caseTactic(nameHint("$" ++ toString(i + 1)),
                          "$" ++ toString(i), false)],
            --solved immediately, as this is a hyp
            [assertTactic(nameHint("$0"), nothing(), top)],
            range(0, num + 1));
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
