grammar extensibella:toAbella:abstractSyntax;

{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   pp, --solely for debugging purposes
   state, debug, displayWidth,
   knownTheorems, knownExtInds, remainingObligations,
   knownTypes, knownRels, knownConstrs,
   provingThms, provingExtInds, duringCommands, afterCommands;


synthesized attribute state::ProofState;
synthesized attribute provingThms::[(QName, Metaterm)];
synthesized attribute debug::Boolean;
synthesized attribute displayWidth::Integer;

--Theorems we have proven and available
--(qualified name, statement)
synthesized attribute knownTheorems::[(QName, Metaterm)];

--ExtInds we have proven and available
--Each sublist is a group of mutually-ext-inded relations
--[[(rel, rel arg names, trans args, trans ty, original, translated)]]
synthesized attribute knownExtInds::[[(QName, [String], [Term], QName, String, String)]];

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
   --approximate maximum line width for display
   displayWidth::Integer
   --theorems we have proven or imported and can use
   --should include the standard library's theorems
   knownThms::[(QName, Metaterm)]
   --extInds we have proven and can use
   knownExtInds::[[(QName, [String], [Term], QName, String, String)]]
   --things we will need to do in the proof based on imports
   obligations::[ThmElement]
   --current environments
   tyEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem>
   --theorems we are currently in the process of proving
   --should be added to knownThms when we finish the proof
   provingThms::[(QName, Metaterm)]
   --extInds we are currently in the process of proving
   --should be added to knownExtInds when we finish the proof
   provingExtInds::[(QName, [String], [Term], QName, String, String)]
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
  top.pp = ppConcat([text("Prover State{"), realLine(),
      text("  Debug Mode:  "), text(toString(debugMode)), realLine(),
      text("  Type Env:  ["), ppImplode(text(", "), map((.pp),
                                 map((.name), tyEnv))), text("]"), realLine(),
      text("  Rel Env:  ["), ppImplode(text(", "), map((.pp),
                                 map((.name), relEnv))), text("]"), realLine(),
      text("  Con Env:  ["), ppImplode(text(", "), map((.pp),
                                map((.name), constrEnv))) ++ text("]"), realLine(),
      text("}"), realLine()]);

  top.state = state;
  top.debug = debugMode;
  top.displayWidth = displayWidth;

  top.knownTheorems = knownThms;
  top.knownExtInds = knownExtInds;

  top.remainingObligations = obligations;

  top.knownTypes = tyEnv;
  top.knownRels = relEnv;
  top.knownConstrs = constrEnv;

  top.provingThms = provingThms;
  top.provingExtInds = provingExtInds;
  top.duringCommands = duringCommands;
  top.afterCommands = afterCommands;
}


--Move all non-extensble obligations from the front of the obligation
--   set and add them to the knownThms
--Leaves everything else the same
--The commands must have already been sent to Abella
function removeNonextensibleObligations
ProverState ::= current::ProverState
{
  local outObligations::[ThmElement] =
      dropWhile((.is_nonextensible), current.remainingObligations);
  local take::[ThmElement] =
      takeWhile((.is_nonextensible), current.remainingObligations);
  local outThms::[(QName, Metaterm)] =
      foldl(\ rest::[(QName, Metaterm)] t::ThmElement ->
              decorate t with {knownThms = rest;}.thms ++ rest,
            current.knownTheorems, take);
  return proverState(current.state, current.debug,
            current.displayWidth, outThms, current.knownExtInds,
            outObligations, current.knownTypes, current.knownRels,
            current.knownConstrs, current.provingThms,
            current.provingExtInds, current.duringCommands,
            current.afterCommands);
}


--Remove an obligation if we finished one, otherwise return the list
--of obligations given
function removeFinishedObligation
[ThmElement] ::=
   obligations::[ThmElement] provenThms::[(QName, Metaterm)]
{
  local newObligations::[ThmElement] =
      case obligations of
      | extensibleMutualTheoremGroup(thms, alsos)::rest ->
        --everything imported here is in the things we just proved
        if all(map(\ t::QName -> contains(t, map(fst, provenThms)),
                   map(fst, thms ++ alsos)))
        then rest
        else obligations
      | translationConstraintTheorem(q, x, b)::rest ->
        case provenThms of
        | [(q2, _)] when q == q2 -> rest
        | _ -> obligations
        end
      | extIndElement(rels)::rest ->
        --everything imported here is in the things we just proved
        if all(map(\ r::QName ->
                     contains(extIndThmName(r), map(fst, provenThms)),
                   map(fst, rels)))
        then rest
        else obligations
      | _ -> obligations
      end;
  return newObligations;
}


--A proof is done successfully, so modify the prover state accordingly
--Assumes current.state is already the one for it being completed
function finishProof
ProverState ::= current::ProverState
{
  return proverState(current.state, current.debug,
            current.displayWidth,
            current.provingThms ++ current.knownTheorems,
            --keep blanks out of the list for efficiency
            if null(current.provingExtInds) then current.knownExtInds
                else current.provingExtInds::current.knownExtInds,
            removeFinishedObligation(current.remainingObligations,
               current.provingThms),
            current.knownTypes, current.knownRels,
            current.knownConstrs, [], [], [], []);
}


--A proof is quit, so modify the prover state accordingly
--Assumes current.state is already the one for it being aborted
function abortProof
ProverState ::= current::ProverState
{
  return proverState(current.state, current.debug,
            current.displayWidth,
            current.knownTheorems, current.knownExtInds,
            current.remainingObligations, current.knownTypes,
            current.knownRels, current.knownConstrs,
            [], [], [], []);
}


--Set debug to debugVal, leaving everything else the same
function setProverDebug
ProverState ::= current::ProverState debugVal::Boolean
{
  return proverState(current.state, debugVal, current.displayWidth,
            current.knownTheorems, current.knownExtInds,
            current.remainingObligations, current.knownTypes,
            current.knownRels, current.knownConstrs,
            current.provingThms, current.provingExtInds,
            current.duringCommands, current.afterCommands);
}


--Set displayWidth to width, leaving everything else the same
function setProverWidth
ProverState ::= current::ProverState width::Integer
{
  return proverState(current.state, current.debug, width,
            current.knownTheorems, current.knownExtInds,
            current.remainingObligations, current.knownTypes,
            current.knownRels, current.knownConstrs,
            current.provingThms, current.provingExtInds,
            current.duringCommands, current.afterCommands);
}


--General updates that might happen in a top command
--Assumes we were not in a proof before
function updateProverStateTop
ProverState ::= current::ProverState newProofState::ProofState
   newThms::[(QName, Metaterm)] newTys::[TypeEnvItem]
   newRels::[RelationEnvItem] newConstrs::[ConstructorEnvItem]
   provingThms::[(QName, Metaterm)]
   provingExtInds::[(QName, [String], [Term], QName, String, String)]
   duringCmds::[(SubgoalNum, [ProofCommand])]
   afterCmds::[AnyCommand]
{
  return proverState(newProofState, current.debug,
            current.displayWidth,
            newThms ++ current.knownTheorems, current.knownExtInds,
            current.remainingObligations,
            addEnv(current.knownTypes, newTys),
            addEnv(current.knownRels, newRels),
            addEnv(current.knownConstrs, newConstrs),
            provingThms, provingExtInds, duringCmds, afterCmds);
}


--Replace only the state in a prover state
function setProofState
ProverState ::= current::ProverState newProofState::ProofState
{
  return proverState(newProofState, current.debug,
            current.displayWidth,
            current.knownTheorems, current.knownExtInds,
            current.remainingObligations, current.knownTypes,
            current.knownRels, current.knownConstrs,
            current.provingThms, current.provingExtInds,
            current.duringCommands, current.afterCommands);
}


--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::= obligations::[ThmElement] tyEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   knownThms::[(QName, Metaterm)]
{
  {-Starting environments with the things from the environment not
    having special syntax to hide them-}
  --types with special constructors can still be seen, so we add them
  local knownTys::[TypeEnvItem] =
      buildEnv(
         [libTypeEnvItem(toQName(pairTypeName), 2),
          libTypeEnvItem(toQName("$lib__nat"), 0),
          libTypeEnvItem(toQName("$lib__bool"), 0),
          libTypeEnvItem(toQName("$lib__integer"), 0),
          libTypeEnvItem(toQName("$char"), 0), --part of strings
          --not our library, but still *a* library
          libTypeEnvItem(toQName("list"), 1),
          libTypeEnvItem(toQName("prop"), 0)]);
  local knownRels::[RelationEnvItem] =
      buildEnv(
         [fixedRelationEnvItem(toQName("is_pair"),
             toTypeList([arrowType(varType("A"), propType),
                         arrowType(varType("B"), propType),
                         pairType(varType("A"), varType("B")),
                         propType])),
          fixedRelationEnvItem(toQName("is_string"),
             toTypeList([stringType(), propType])),
          fixedRelationEnvItem(toQName("is_bool"),
             toTypeList([boolType, propType])),
          fixedRelationEnvItem(toQName("is_integer"),
             toTypeList([integerType, propType])),
          fixedRelationEnvItem(toQName("is_list"),
             toTypeList([arrowType(varType("A"), propType),
                         listType(varType("A")), propType])),
          --need hidden relations due to how we handle importing from
          --one module to another one
          fixedRelationEnvItem(toQName(integerAdditionName),
             toTypeList([integerType, integerType, integerType])),
          fixedRelationEnvItem(toQName(integerSubtractionName),
             toTypeList([integerType, integerType, integerType])),
          fixedRelationEnvItem(toQName(integerMultiplicationName),
             toTypeList([integerType, integerType, integerType])),
          fixedRelationEnvItem(toQName(integerDivisionName),
             toTypeList([integerType, integerType, integerType])),
          fixedRelationEnvItem(toQName(integerModulusName),
             toTypeList([integerType, integerType, integerType])),
          fixedRelationEnvItem(toQName(integerNegateName),
             toTypeList([integerType, integerType])),
          fixedRelationEnvItem(toQName(integerLessName),
             toTypeList([integerType, integerType])),
          fixedRelationEnvItem(toQName(integerLessEqName),
             toTypeList([integerType, integerType])),
          fixedRelationEnvItem(toQName(integerGreaterName),
             toTypeList([integerType, integerType])),
          fixedRelationEnvItem(toQName(integerGreaterEqName),
             toTypeList([integerType, integerType])),
          fixedRelationEnvItem(toQName(appendName),
             toTypeList([listType(varType("A")),
                         listType(varType("A")),
                         listType(varType("A"))])),
          fixedRelationEnvItem(toQName(orName),
             toTypeList([boolType, boolType, boolType])),
          fixedRelationEnvItem(toQName(andName),
             toTypeList([boolType, boolType, boolType])),
          fixedRelationEnvItem(toQName(notName),
             toTypeList([boolType, boolType])),
          fixedRelationEnvItem(toQName("acc"),
             toTypeList([integerType, integerType])),
          --once again, not our library, but *a* library
          fixedRelationEnvItem(toQName("member"),
             toTypeList([varType("A"),
                         listType(varType("A")), propType]))
         ]);
    local knownConstrs::[ConstructorEnvItem] =
        buildEnv(
            --hidden pair constructor
           [constructorEnvItem(toQName(pairConstructorName),
               pairType(varType("A"), varType("B")),
               toTypeList([varType("A"), varType("B")])),
            --hidden integer constructors
            constructorEnvItem(toQName(posIntegerName),
               integerType,
               toTypeList([nameType(toQName("$lib__nat"))])),
            constructorEnvItem(toQName(negIntegerName),
               integerType,
               toTypeList([nameType(toQName("$lib__nat"))])),
            --hidden nat constructors
            constructorEnvItem(toQName(natSuccName),
               nameType(toQName("$lib__nat")),
               toTypeList([nameType(toQName("$lib__nat"))])),
            constructorEnvItem(toQName(natZeroName),
               nameType(toQName("$lib__nat")), toTypeList([]))
           ]);

  return proverState(noProof(), false, 80, knownThms, [], obligations,
            addEnv(tyEnv, knownTys), addEnv(relEnv, knownRels),
            addEnv(constrEnv, knownConstrs), [], [], [], []);
}


--Drop a duringCommand from the beginning, leaving all else the same
--This should only be used when the first command has just run
function dropDuringCommand
ProverState ::= p::ProverState
{
  return proverState(p.state, p.debug, p.displayWidth,
            p.knownTheorems, p.knownExtInds,
            p.remainingObligations, p.knownTypes, p.knownRels,
            p.knownConstrs, p.provingThms, p.provingExtInds,
            tail(p.duringCommands), p.afterCommands);
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

--Find an ExtInd declaration group including rel
function findExtIndGroup
Maybe<[(QName, [String], [Term], QName, String, String)]> ::=
   name::QName state::ProverState
{
  local find::[[(QName, [String], [Term], QName, String, String)]] =
      filter(\ l::[(QName, [String], [Term], QName, String, String)] ->
               contains(name, map(fst, l)),
             state.knownExtInds);
  return case find of
         | [] -> nothing()
         | [x] -> just(x)
         | _ -> error("findExtIndGroup impossible")
         end;
}
