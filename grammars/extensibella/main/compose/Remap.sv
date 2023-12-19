grammar extensibella:main:compose;

--[(old hyp name, name hyp name, is now R_T)]
inherited attribute mapHyps::[(String, String, Boolean)];
--[(old var name, new term)]
inherited attribute mapVars::[(String, Term)];
--result of mapping
functor attribute mapped;
synthesized attribute mappedCmds::[ProofCommand];

--theorem names and statements
inherited attribute allThms::[(QName, Metaterm)];
--original hypotheses and new ones
inherited attribute oldHyps::[(String, Metaterm)];
inherited attribute newHyps::[(String, Metaterm)];
--key relations in current theorem set
inherited attribute keyRels::[QName];


attribute
   mapHyps, mapVars, mappedCmds, allThms, oldHyps, newHyps, keyRels
occurs on AnyCommand, ProofCommand, ApplyArgs, ApplyArg;
attribute
   mapHyps, mapVars, mapped
occurs on Metaterm;
attribute
   mapVars, mapped
occurs on Term, Withs, EWitnesses, EWitness,
   SearchWitness;
attribute
   mapHyps, mapped, keyRels, allThms, oldHyps, newHyps
occurs on Clearable;
attribute
   mapped
occurs on ApplyArg, ApplyArgs;

propagate allThms, oldHyps, newHyps, keyRels on
   AnyCommand, ProofCommand, ApplyArgs, ApplyArg;
propagate mapHyps on AnyCommand, ProofCommand, Metaterm, Clearable,
   ApplyArgs, ApplyArg;
propagate mapVars on AnyCommand, ProofCommand, Metaterm, Term,
   Withs, ApplyArgs, ApplyArg, EWitnesses, EWitness, SearchWitness;
propagate mapped on Metaterm, Term, ApplyArgs, EWitnesses, EWitness,
   SearchWitness excluding applyTactic, caseTactic, nameTerm;


aspect production anyTopCommand
top::AnyCommand ::= t::TopCommand
{
  top.mappedCmds = [];
}


aspect production anyProofCommand
top::AnyCommand ::= p::ProofCommand
{
  top.mappedCmds = p.mappedCmds;
}


aspect production anyNoOpCommand
top::AnyCommand ::= n::NoOpCommand
{
  top.mappedCmds = [];
}


aspect production anyParseFailure
top::AnyCommand ::= msg::String
{
  top.mappedCmds = [];
}





aspect production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.mappedCmds = [top];
}


aspect production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.mappedCmds = [top];
}


aspect production introsTactic
top::ProofCommand ::= names::[String]
{
  top.mappedCmds = [top];
}


aspect production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::ApplyArgs withs::Withs
{
  withs.mapBindingNames = theorem.hypNameMap;

  --currently ignoring R to R_T change
  top.mappedCmds = [applyTactic(h, depth, theorem.mapped,
                                args.mapped, withs.mapped)];
}


aspect production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable
                      withs::Withs
{
  withs.mapBindingNames = theorem.hypNameMap;

  --currently ignoring R to R_T change
  top.mappedCmds =
      [backchainTactic(depth, theorem.mapped, withs.mapped)];
}


aspect production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.mappedCmds =
      [caseTactic(h, lookup(hyp, top.mapHyps).fromJust.1, keep)];
}


aspect production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  top.mappedCmds = [assertTactic(h, depth, m.mapped)];
}


aspect production existsTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.mappedCmds = [existsTactic(ew.mapped)];
}


aspect production witnessTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.mappedCmds = [witnessTactic(ew.mapped)];
}


aspect production searchTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.mappedCmds = [top];
}


aspect production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.mappedCmds = [searchWitnessTactic(sw.mapped)];
}


aspect production asyncTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production splitTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production splitStarTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production leftTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production rightTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production skipTactic
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production abortCommand
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production undoCommand
top::ProofCommand ::=
{
  top.mappedCmds = [top];
}


aspect production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.mappedCmds =
      [clearCommand(
          map(\ x::String -> lookup(x, top.mapHyps).fromJust.1,
              removes), hasArrow)];
}


aspect production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  --Renaming things does not necessarily work when things are mapped.
  --It could cause problems if renamed is now an existing name.
  --Therefore do nothing here and let the proof state mapping take
  --   care of the changes.
  top.mappedCmds = [];
}


aspect production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  top.mappedCmds = error("no abbrev");
}


aspect production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  top.mappedCmds = error("no unabbrev");
}


aspect production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  top.mappedCmds = error("no permute");
}


aspect production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.mappedCmds = [top];
}


aspect production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.mappedCmds = [top];
}


aspect production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.mappedCmds = [top];
}


aspect production computeTactic
top::ProofCommand ::= hyp::String
{
  top.mappedCmds = error("computeTactic should not be present");
}





--map old bound names to new ones
--e.g. `forall a b c, ...` and `forall a d e, ...` ->
--     [(a, a), (b, d), (c, e)]
synthesized attribute hypNameMap::[(String, String)] occurs on Clearable;
--whether each premise expects R_T
synthesized attribute expectTransRel::[Boolean] occurs on Clearable;
--whether each premise expects a key relation in the non-R_T style
synthesized attribute expectBasicKeyRel::[Boolean] occurs on Clearable;

aspect production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  top.mapped =
      clearable(star,
         if hyp.isQualified then hyp
         else toQName(lookup(hyp.shortName, top.mapHyps).fromJust.1),
         instantiation);

  top.hypNameMap =
      if hyp.isQualified
      then [] --names in theorems don't change
      else hypNameMap;

  local m::Metaterm = if hyp.isQualified then thmM else hypNewM;
  local msplits::[Metaterm] =
      case m of
      | bindingMetaterm(_, _, body) -> body.splitImplies
      | _ -> m.splitImplies
      end;
  top.expectTransRel =
      map(\ m::Metaterm ->
            case m of
            | transRelMetaterm(_, _, _) -> true --R_T expected
            | _ -> false --R_T not expected
            end, msplits);
  top.expectBasicKeyRel =
      map(\ m::Metaterm ->
            case m of
            | relationMetaterm(q, _, _) -> contains(q, top.keyRels)
            | _ -> false
            end, msplits);

  local thmM::Metaterm =
      lookup(hyp, top.allThms).fromJust;

  local hypOldM::Metaterm =
      lookup(hyp.shortName, top.oldHyps).fromJust;
  local hypNewM::Metaterm =
      lookup(lookup(hyp.shortName, top.mapHyps).fromJust.1,
             top.newHyps).fromJust;
  local hypNameMap::[(String, String)] =
      case hypOldM, hypNewM of
      | bindingMetaterm(_, oldB, _), bindingMetaterm(_, newB, _) ->
        zip(map(fst, oldB.toList), map(fst, newB.toList))
      | _, _ -> []
      end;
}





--whether each arg is supposed to be R as opposed to R_T for some key
--   relation in this group
inherited attribute basicKeyRelExpectations::[Boolean]
   occurs on ApplyArgs;
inherited attribute basicKeyRelExpected::Boolean occurs on ApplyArg;

aspect production endApplyArgs
top::ApplyArgs ::=
{
  top.mappedCmds = [];
}


aspect production addApplyArgs
top::ApplyArgs ::= a::ApplyArg rest::ApplyArgs
{
  top.mappedCmds = a.mappedCmds ++ rest.mappedCmds;

  a.basicKeyRelExpected = head(top.basicKeyRelExpectations);
  rest.basicKeyRelExpectations = tail(top.basicKeyRelExpectations);
}



aspect production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  top.mapped = hypApplyArg(newHyp, instantiation);

  local newHyp::String = lookup(hyp, top.mapHyps).fromJust.1;
  local newHypIsTrans::Boolean =
      case lookup(newHyp, top.newHyps) of
      | just(transRelMetaterm(_, _, _)) -> true
      | _ -> false
      end;
  local newHypRel::QName =
      case lookup(newHyp, top.newHyps) of
      | just(transRelMetaterm(q, _, _)) -> q
      | _ -> error("Should not access (hypApplyArg)")
      end;
  local genName::String = "$" ++ toString(genInt());
  top.mappedCmds =
      if top.basicKeyRelExpected && newHypIsTrans
      then [applyTactic(nameHint(genName), nothing(),
               clearable(false, drop_ext_ind_name(newHypRel),
                         emptyTypeList()),
               addApplyArgs(hypApplyArg(newHyp, emptyTypeList()),
                  endApplyArgs()), endWiths())]
      else [];
}


aspect production starApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  top.mapped = starApplyArg(newHyp, instantiation);

  local newHyp::String = lookup(hyp, top.mapHyps).fromJust.1;
  local newHypIsTrans::Boolean =
      case lookup(newHyp, top.newHyps) of
      | just(transRelMetaterm(_, _, _)) -> true
      | _ -> false
      end;
  local newHypRel::QName =
      case lookup(newHyp, top.newHyps) of
      | just(transRelMetaterm(q, _, _)) -> q
      | _ -> error("Should not access (hypApplyArg)")
      end;
  local genName::String = "$" ++ toString(genInt());
  top.mappedCmds =
      if top.basicKeyRelExpected && newHypIsTrans
      then [applyTactic(nameHint(genName), nothing(),
               clearable(false, drop_ext_ind_name(newHypRel),
                         emptyTypeList()),
               addApplyArgs(hypApplyArg(newHyp, emptyTypeList()),
                  endApplyArgs()), endWiths())]
      else [];
}





--map changes to binding names
--e.g. if we have `forall a b c, ...` in the old and that corresponds
--     to `forall a d e, ...` in the new, then mapBindingNames is
--     something like [(b, d), (c, e)]
inherited attribute mapBindingNames::[(String, String)]
   occurs on Withs;
propagate mapBindingNames on Withs;

aspect production endWiths
top::Withs ::=
{
  top.mapped = top;
}


aspect production addWiths
top::Withs ::= name::String term::Term rest::Withs
{
  top.mapped = addWiths(
                  case lookup(name, top.mapBindingNames) of
                  | just(n) -> n
                  | nothing() -> name --no change
                  end, term.mapped, rest.mapped);
}





aspect production nameTerm
top::Term ::= name::QName mty::MaybeType
{
  top.mapped =
      if name.isQualified
      then top
      else case lookup(name.shortName, top.mapVars) of
           | just(t) -> t
           | _ -> top
           end;
}





aspect production existsSearchWitness
top::SearchWitness ::= withs::Withs sub::SearchWitness
{
  withs.mapBindingNames = [];
}
