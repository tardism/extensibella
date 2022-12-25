grammar extensibella:toAbella:abstractSyntax;

--import extensibella:thmInterfaceFile:abstractSyntax;

{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, provingThms, debug, knownTheorems, remainingObligations,
   replaceState, replacedState<ProverState>;


synthesized attribute state::ProofState;
synthesized attribute provingThms::[(QName, Metaterm)];
synthesized attribute debug::Boolean;

--Theorems we have proven and available
--(qualified name, statement)
synthesized attribute knownTheorems::[(QName, Metaterm)];

--
synthesized attribute remainingObligations::[ThmElement];


abstract production proverState
top::ProverState ::=
   state::ProofState provingThms::[(QName, Metaterm)]
   debugMode::Boolean
   thms::[(QName, Metaterm)]
   obligations::[ThmElement]
{
  top.state = state;
  top.provingThms = provingThms;
  top.debug = debugMode;

  top.knownTheorems = thms;

  top.remainingObligations = obligations;

  --Determine whether we need to remove an extensible mutual group
  --   from the beginning because we just proved it
  local newObligations::[ThmElement] =
        case obligations of
        | extensibleMutualTheoremGroup(thms)::rest ->
          if map(\ p::(String, String, Metaterm) -> p.2 ++ ":" ++ p.1,
                 provingThms) ==
             map(fst, thms)
          then rest
          else obligations
        | _ -> obligations
        end;
  top.replacedState =
      case top.replaceState of
      | proofCompleted() ->
        proverState(top.replaceState, [], debugMode,
                    provingThms ++ thms, newObligations)
      | proofAborted() ->
        proverState(top.replaceState, [], debugMode, thms,
                    obligations)
      | _ ->
        proverState(top.replaceState, provingThms, debugMode,
                    thms, obligations)
      end;
}



--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::= obligations::[String] --[ThmElement]
{
  --The metaterms won't be needed, so we can just leave them out
  local knownThms1::[(String, String, Metaterm)] =
        [
         --strings.thm
         (toQName("extensibella:stdLib:is_string_append"), trueMetaterm()),
         (toQName("extensibella:stdLib:is_string_eq_or_not"), trueMetaterm()),
         --bools.thm
         (toQName("extensibella:stdLib:is_bool_eq_or_not"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_comm"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_true_left"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_true_left_eq"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_true_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_true_right_eq"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_false_left"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_false_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_associative"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_idempotent"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_comm"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_true_left"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_true_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_false_left"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_false_left_eq"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_false_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_false_right_eq"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_associative"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_idempotent"), trueMetaterm()),
         (toQName("extensibella:stdLib:not_bool_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:not_bool_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:not_bool_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:not_bool_double_negation"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool_complementation"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool_complementation"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool" ++ name_sep ++
                  "distribute_over" ++ name_sep ++ "or"), trueMetaterm()),
         (toQName("extensibella:stdLib:and_bool" ++ name_sep ++
                  "undistribute_over" ++ name_sep ++ "or"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool" ++ name_sep ++
                  "distribute_over" ++ name_sep ++ "and"), trueMetaterm()),
         (toQName("extensibella:stdLib:or_bool" ++ name_sep ++
                  "undistribute_over" ++ name_sep ++ "and"), trueMetaterm()),
         (toQName("extensibella:stdLib:DeMorgan" ++ name_sep ++
                  "not_bool" ++ name_sep ++ "and_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:DeMorgan" ++ name_sep ++
                  "or_bool" ++ name_sep ++ "not_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:DeMorgan" ++ name_sep ++
                  "not_bool" ++ name_sep ++ "or_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:DeMorgan" ++ name_sep ++
                  "and_bool" ++ name_sep ++ "not_bool"), trueMetaterm())
        ];
  local knownThms2::[(String, String, Metaterm)] =
        [
         --integers.thm
         (toQName("extensibella:stdLib:is_integer_eq_or_not"), trueMetaterm()),
         --integer_addition.thm
         (toQName("extensibella:stdLib:plus_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_is_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_comm"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_assoc"), trueMetaterm()),
         (toQName("extensibella:stdLib:minus_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:minus_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:minus_integer_is_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:minus_integer_same"), trueMetaterm()),
         (toQName("extensibella:stdLib:minus_integer_0"), trueMetaterm()),
         (toQName("extensibella:stdLib:negate_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:negate_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:negate_integer_is_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:negate_integer_double"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_0_result"), trueMetaterm()),
         (toQName("extensibella:stdLib:plus_integer_negatives"), trueMetaterm()),
         --integer_multiplication.thm
         (toQName("extensibella:stdLib:multiply_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_is_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_0_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_1"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_1_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_0_result"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_-1_negate"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_negation"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_comm"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_distribute_over_plus"),
             trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_assoc"), trueMetaterm()),
         (toQName("extensibella:stdLib:multiply_integer_undistribute_over_plus"),
             trueMetaterm()),
         --integer_comparison.thm
         (toQName("extensibella:stdLib:less_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:less_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:less_integer_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:lesseq_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:lesseq_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:lesseq_integer_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:eq_to_lesseq_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:less_to_lesseq_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:greater_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:greater_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:greater_integer_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:greatereq_integer_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:greatereq_integer_total"), trueMetaterm()),
         (toQName("extensibella:stdLib:greatereq_integer_is_bool"), trueMetaterm()),
         (toQName("extensibella:stdLib:eq_to_greatereq_integer"), trueMetaterm()),
         (toQName("extensibella:stdLib:greater_to_greatereq_integer"), trueMetaterm()),
         --lists.thm
         (toQName("extensibella:stdLib:append_nil_right"), trueMetaterm()),
         (toQName("extensibella:stdLib:append_nil_left"), trueMetaterm()),
         (toQName("extensibella:stdLib:append_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:head_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:tail_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:length_unique"), trueMetaterm()),
         (toQName("extensibella:stdLib:null_unique"), trueMetaterm())
        ];
  production attribute knownThms::[(String, String, Metaterm)] with ++;
  knownThms := knownThms1 ++ knownThms2;
  --Prop-quantified theorems handled by asserting for the particular
  --   case, then applying
  knownThms <-
     [
      (toQName("extensibella:stdLib:is_list_member"), trueMetaterm()),
      (toQName("extensibella:stdLib:is_list_append"), trueMetaterm()),
      (toQName("extensibella:stdLib:symmetry"), trueMetaterm())
     ];
  return proverState(noProof(), [], false, true, [], --knownThms,
                     obligations);
}


--(full name, statement)
function findTheorem
[(QName, Metaterm)] ::= name::QName state::ProverState
{
  return
     filter(
        if name.isQualified
        then \ p::(QName, Metaterm) -> p.1 == name
        else \ p::(QName, Metaterm) -> p.1.shortName == name.shortName,
        state.knownTheorems);
}
