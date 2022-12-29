grammar extensibella:toAbella:abstractSyntax;

{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, debug, knownTheorems, remainingObligations,
   knownTypes, knownRels, knownConstrs,
   provingThms, duringCommands, afterCommands,
   replaceState, replacedState<ProverState>;


synthesized attribute state::ProofState;
synthesized attribute provingThms::[(QName, Metaterm)];
synthesized attribute debug::Boolean;

--Theorems we have proven and available
--(qualified name, statement)
synthesized attribute knownTheorems::[(QName, Metaterm)];

--Things we will need to do in the proof based on imports that we
--haven't done yet
synthesized attribute remainingObligations::[ThmElement];

--Environments of various entities we know
synthesized attribute knownTypes::Env<TypeEnvItem>;
synthesized attribute knownRels::Env<RelationEnvItem>;
synthesized attribute knownConstrs::Env<ConstructorEnvItem>;


abstract production proverState
top::ProverState ::=
   --current state of Abella
   state::ProofState
   --whether to print out the Abella commands/returns to the user
   debugMode::Boolean
   --theorems we have proven or imported and can use
   --should include the standard library's theorems
   knownThms::[(QName, Metaterm)]
   --things we will need to do in the proof based on imports
   obligations::[ThmElement]
   --current environments
   tyEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem>
   --theorems we are currently in the process of proving
   --should be added to knownThms when we finish the proof
   provingThms::[(QName, Metaterm)]
   --things to do when the subgoal reaches that number
   --should clear it once it has been sent to Abella
   --Note:  If there are commands for e.g. Subgoal 2 that are expected
   --  to move us to Subgoal 2.1, there should not be a separate entry
   --  for Subgoal 2.1.  Any sequential commands should be rolled into
   --  a single entry because we don't want to need to check this
   --  repeatedly.
   duringCommands::[(SubgoalNum, [ProofCommand])]
   --things to do when the proof is done
   --I think this is only ever one Split, but make it general in case
   afterCommands::[AnyCommand]
{
  top.state = state;
  top.debug = debugMode;

  top.knownTheorems = knownThms;

  top.remainingObligations = obligations;

  top.knownTypes = tyEnv;
  top.knownRels = relEnv;
  top.knownConstrs = constrEnv;

  top.provingThms = provingThms;
  top.duringCommands = duringCommands;
  top.afterCommands = afterCommands;

  --Determine whether we need to remove an extensible mutual group
  --   from the beginning because we just proved it
  local newObligations::[ThmElement] =
        case obligations of
        | extensibleMutualTheoremGroup(thms)::rest ->
          --everything imported here is in the things we just proved
          if all(map(\ t::QName -> contains(t, map(fst, provingThms)),
                     map(fst, thms)))
          then rest
          else obligations
        | _ -> obligations
        end;
  top.replacedState =
      case top.replaceState of
      | proofCompleted() ->
        proverState(top.replaceState, debugMode,
                    provingThms ++ knownThms, newObligations,
                    tyEnv, relEnv, constrEnv, [], [], afterCommands)
      | proofAborted() ->
        proverState(top.replaceState, debugMode, knownThms,
                    obligations, tyEnv, relEnv, constrEnv, [], [], [])
      | _ when !null(duringCommands) &&
               subgoalLess(head(duringCommands).1,
                           top.replaceState.currentSubgoal) ->
        proverState(top.replaceState, debugMode, knownThms,
                    obligations, tyEnv, relEnv, constrEnv,
                    provingThms, tail(duringCommands), afterCommands)
      | _ ->
        proverState(top.replaceState, debugMode, knownThms,
                    obligations, tyEnv, relEnv, constrEnv,
                    provingThms, duringCommands, afterCommands)
      end;
}



--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::= obligations::[ThmElement] tyEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
{
  --The metaterms won't be needed, so we can just leave them out
  local knownThms1::[(QName, Metaterm)] =
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
  local knownThms2::[(QName, Metaterm)] =
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
  production attribute knownThms::[(QName, Metaterm)] with ++;
  knownThms := knownThms1 ++ knownThms2;
  --Prop-quantified theorems handled by asserting for the particular
  --   case, then applying
  knownThms <-
     [
      (toQName("extensibella:stdLib:is_list_member"), trueMetaterm()),
      (toQName("extensibella:stdLib:is_list_append"), trueMetaterm()),
      (toQName("extensibella:stdLib:symmetry"), trueMetaterm())
     ];

  {-Starting environments with the things from the environment not
    having special syntax to hide them-}
  --types with special constructors can still be seen, so we add them
  local knownTys::[TypeEnvItem] =
      buildEnv(
         [libTypeEnvItem(toQName(pairTypeName), 2),
          libTypeEnvItem(toQName("$lib__nat"), 0),
          libTypeEnvItem(toQName("$lib__bool"), 0),
          libTypeEnvItem(toQName("$lib__integer"), 0),
          --not our library, but still *a* library
          libTypeEnvItem(toQName("list"), 1)]);
  --a couple of these have type variables in them
  local knownRels::[RelationEnvItem] =
      buildEnv(
         [fixedRelationEnvItem(toQName("is_pair"),
             toTypeList([arrowType(nameType(toQName("A")),
                                   nameType(toQName("prop"))),
                         arrowType(nameType(toQName("B")),
                                   nameType(toQName("prop"))),
                         functorType(
                         functorType(nameType(toQName(pairTypeName)),
                                     nameType(toQName("A"))),
                                     nameType(toQName("B")))])),
          fixedRelationEnvItem(toQName("is_string"),
             toTypeList([stringType])),
          fixedRelationEnvItem(toQName("is_bool"),
             toTypeList([nameType(toQName("$lib__bool"))])),
          fixedRelationEnvItem(toQName("is_integer"),
             toTypeList([nameType(toQName("$lib__integer"))])),
          fixedRelationEnvItem(toQName("is_list"),
             toTypeList([arrowType(nameType(toQName("A")),
                                   nameType(toQName("prop"))),
                         functorType(nameType(toQName("list")),
                                     nameType(toQName("A")))])),
          --once again, not our library, but *a* library
          fixedRelationEnvItem(toQName("member"),
             toTypeList([nameType(toQName("A")),
                         functorType(nameType(toQName("list")),
                                     nameType(toQName("A")))]))]);
  --currently no visible constructors from the standard library
  local knownConstrs::[ConstructorEnvItem] = buildEnv([]);

  return proverState(noProof(), false, knownThms, obligations,
            addEnv(tyEnv, knownTys), addEnv(relEnv, knownRels),
            addEnv(knownConstrs, knownConstrs), [], [], []);
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
