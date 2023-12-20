grammar extensibella:main:compose;

function buildExtThmProofs
IOVal<[String]> ::=
   --[(thm name, key relation, property is host-y, bindings, body,
   --  key relation intros name)]
   thmsInfo::[(QName, RelationEnvItem, Boolean, Bindings, ExtBody,
               String)]
       --[(mod name, proof stuff grouped by all subgoals)]
   topGoalProofInfo::[(QName, [[(ProofState, [AnyCommand])]])]
   allThms::[(QName, Metaterm)] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   abella::ProcessHandle config::Configuration
   parsers::AllParsers ioin::IOToken
{
  local fstThm::(QName, RelationEnvItem, Boolean, Bindings,
                 ExtBody, String) = head(thmsInfo);

  local intros_case::String =
      let prems::[(Maybe<String>, Metaterm)] =
        decorate fstThm.5 with {
           typeEnv = error("typeEnv not needed");
           relationEnv = error("relationEnv not needed");
           constructorEnv = error("constructorEnv not needed");
           boundNames = fstThm.4.usedNames;
        }.premises
      in
        "intros " ++
        implode(" ",
           generateExtIntrosNames(catMaybes(map(fst, prems)),
              prems)) ++ ". " ++
        fstThm.6 ++ ": case " ++ fstThm.6 ++ " (keep)."
      end;
  local intros_case_to_abella::IOVal<String> =
      sendBlockToAbella(intros_case, abella, ioin, config);

  local thisMod::[[(ProofState, [AnyCommand])]] =
      --module must exist, so .fromJust is valid
      lookup(fstThm.1.moduleName, topGoalProofInfo).fromJust;
  --root number for subgoal for this thm
  local subgoalNum::SubgoalNum =
      --no empty lists in this, so head is valid
      subgoalRoot(head(head(thisMod)).1.currentSubgoal);


  --Host Theorem Proof
  --get commands, update remaining part
  local host_gathering::([String],
                         [(QName, [[(ProofState, [AnyCommand])]])]) =
      foldr(\ here::(QName, [[(ProofState, [AnyCommand])]])
              rest::([String],
                     [(QName, [[(ProofState, [AnyCommand])]])]) ->
              case here.2 of
              | ((s, _)::_)::_ when subgoalStartsWith(subgoalNum,
                                       s.currentSubgoal) ->
                let sub::([[String]], [[(ProofState, [AnyCommand])]]) =
                    takeAllRootedBySubgoal(here.2, subgoalNum)
                in
                  (implode("\n  ",
                      map(\ l::[String] -> implode(" ", l),
                          sub.1))::rest.1,
                   (here.1, sub.2)::rest.2)
                end
              | _ -> (rest.1, here::rest.2) --no proof here
              end,
            ([], []), topGoalProofInfo);
  local host_string::String =
      intros_case ++ "\n  " ++
      implode("\n  ", host_gathering.1);
  local host_to_abella::IOVal<String> =
      sendBlockToAbella(host_string, abella, intros_case_to_abella.io,
                        config);
  local host_rest::IOVal<[String]> =
      buildExtThmProofs(tail(thmsInfo), host_gathering.2, allThms,
         typeEnv, relEnv, constrEnv, abella, config, parsers,
         host_to_abella.io);


  --Extension Theorem Proof
  local extSplitCases::([[[(ProofState, [AnyCommand])]]],
                        [[(ProofState, [AnyCommand])]]) =
      getFullRootedBySubgoal(thisMod, subgoalNum);
  --known cases are all but last one
  local extKnownCases::[[[(ProofState, [AnyCommand])]]] =
      init(extSplitCases.1);
  --preservability proof is the last one done
  local extPreservabilityCase::[[(ProofState, [AnyCommand])]] =
      last(extSplitCases.1);
  local keyRels::[QName] =
      map(\ p::(QName, RelationEnvItem, Boolean, Bindings, ExtBody,
                String) -> p.2.name, thmsInfo);
  --proof state after thm set-up
  local initProofState::ProofState =
      fullStateProcessing(intros_case_to_abella.iovalue, typeEnv,
         relEnv, constrEnv, parsers);
  --run through the case commands, building the proof
  local extRun::IOVal<([[String]], ProofState)> =
      buildExtensionThmProof(extKnownCases, extPreservabilityCase,
         subgoalNum, abella, config, parsers, initProofState,
         allThms, keyRels, typeEnv, relEnv, constrEnv,
         intros_case_to_abella.io);
  --update for use in proving the rest of the theorems
  local extUpdatedGoalInfo::[(QName, [[(ProofState, [AnyCommand])]])] =
      updateAssoc(topGoalProofInfo, fstThm.1.moduleName,
                  extSplitCases.2);
  --put the commands together into a single string
  local ext_string::String =
      intros_case ++ "\n  " ++
      implode("\n  ",
          map(\ l::[String] -> implode(" ", l), extRun.iovalue.1));
  local ext_rest::IOVal<[String]> =
      buildExtThmProofs(tail(thmsInfo), extUpdatedGoalInfo, allThms,
         typeEnv, relEnv, constrEnv, abella, config, parsers,
         extRun.io);


  return
      case thmsInfo of
      | [] -> ioval(ioin, [])
      | _::rest ->
        if fstThm.3
        then ioval(host_rest.io, host_string::host_rest.iovalue)
        else ioval(ext_rest.io, ext_string::ext_rest.iovalue)
      end;
}


--get all the commands starting with a certain subgoal number, but
--   group them by subgoals under that
function takeAllRootedBySubgoal
([[String]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   root::SubgoalNum
{
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        let sub::([String], [[(ProofState, [AnyCommand])]]) =
            takeAllRooted(cmdStates, head(l).1.currentSubgoal)
        in
        let again::([[String]], [[(ProofState, [AnyCommand])]]) =
            takeAllRootedBySubgoal(sub.2, root)
        in
          (sub.1::again.1, again.2)
        end end
      | _ -> ([], cmdStates)
      end;
}


--get all the commands starting with a certain subgoal number, as well
--   as the remnant
--e.g. for numRoot = 1.1, gets commands for 1.1, 1.1.1, 1.1.3.1, but
--     not 1, 1.2, 3
function takeAllRooted
([String], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   numRoot::SubgoalNum
{
  local sub::([String], [[(ProofState, [AnyCommand])]]) =
      takeAllRooted(tail(cmdStates), numRoot);
  return
      case cmdStates of
      | x::rest when
        subgoalStartsWith(numRoot, head(x).1.currentSubgoal) ->
        (implode(" ", map((.abella_pp), flatMap(snd, x)))::sub.1,
         sub.2)
      | _ -> ([], cmdStates)
      end;
}


--get all the command states starting with a certain subgoal number,
--   but group them by subgoals under that
function getFullRootedBySubgoal
([[[(ProofState, [AnyCommand])]]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]]
   root::SubgoalNum
{
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        let sub::([[(ProofState, [AnyCommand])]],
                  [[(ProofState, [AnyCommand])]]) =
            getFullRooted(cmdStates, head(l).1.currentSubgoal)
        in
        let again::([[[(ProofState, [AnyCommand])]]],
                    [[(ProofState, [AnyCommand])]]) =
            getFullRootedBySubgoal(sub.2, root)
        in
          (sub.1::again.1, again.2)
        end end
      | _ -> ([], cmdStates)
      end;
}


--get all the command states starting with a certain subgoal number,
--   and the remnant
function getFullRooted
([[(ProofState, [AnyCommand])]], [[(ProofState, [AnyCommand])]]) ::=
   cmdStates::[[(ProofState, [AnyCommand])]] root::SubgoalNum
{
  local sub::([[(ProofState, [AnyCommand])]],
              [[(ProofState, [AnyCommand])]]) =
      getFullRooted(tail(cmdStates), root);
  return
      case cmdStates of
      | l::rest when
        subgoalStartsWith(root, head(l).1.currentSubgoal) ->
        (l::sub.1, sub.2)
      | _ -> ([], cmdStates)
      end;
}




function updateAssoc
Eq a => [(a, b)] ::= l::[(a, b)] key::a value::b
{
  return if head(l).1 == key then (key, value)::tail(l)
                             else updateAssoc(tail(l), key, value);
}



function buildExtensionThmProof
IOVal<([[String]], ProofState)> ::=
   knownCases::[[[(ProofState, [AnyCommand])]]]
   preservabilityCase::[[(ProofState, [AnyCommand])]]
   rootSubgoal::SubgoalNum abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  local origState::ProofState = head(head(head(knownCases))).1;
  origState.mapTo = incomingState;
  origState.typeEnv = typeEnv;
  origState.relationEnv = relEnv;
  origState.constructorEnv = constrEnv;

  --when the current composed case is one of the known cases
  local runKnown::IOVal<([String], ProofState)> =
      runKnownCase(head(knownCases), abella, config, parsers,
         incomingState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, ioin);
  local subKnown::IOVal<([[String]], ProofState)> =
      buildExtensionThmProof(tail(knownCases), preservabilityCase,
         rootSubgoal, abella, config, parsers, runKnown.iovalue.2,
         allThms, keyRels, typeEnv, relEnv, constrEnv, runKnown.io);

  --when the current composed case is one of the unknown cases
  local runPres::IOVal<([String], ProofState)> =
      runPreservabilityCase(preservabilityCase, abella, config,
         parsers, incomingState, allThms, keyRels, typeEnv,
         relEnv, constrEnv, ioin);
  local subPres::IOVal<([[String]], ProofState)> =
      buildExtensionThmProof(knownCases, preservabilityCase,
         rootSubgoal, abella, config, parsers,
         runPres.iovalue.2, allThms, keyRels, typeEnv, relEnv,
         constrEnv, runPres.io);

  return
      if !subgoalStartsWith(rootSubgoal,
                            incomingState.currentSubgoal) ||
         !incomingState.inProof
      then ioval(ioin, ([], incomingState))
      else {-
             Taking known proof cases whenever they fit guarantees we
             can build the proof.  All the host cases come first, and
             in the same order as in the modular proofs, so we clear
             them first.
      
             The remaining cases are those introduced by extensions.
             These must have a constructor for the primary component.
             Then the proof states for known extension cases can only
             unify with the composed proof states for the same cases;
             those for other extensions cannot unify because they have
             a different PC constructor.
      
             Thus taking a known case whenever it unifies guarantees
             we map each of the known proofs to the correct known
             cases in the composed proof, and each known proof case is
             at the front of the list when it comes up.  Then if the
             head of the known cases does not unify, the
             preservability case must be applicable.
           -}
           case knownCases of
           | _::_ when origState.mapSuccess ->
             ioval(subKnown.io,
                   (runKnown.iovalue.1::subKnown.iovalue.1,
                    subKnown.iovalue.2))
           | _ ->
             ioval(subPres.io,
                   (runPres.iovalue.1::subPres.iovalue.1,
                    subPres.iovalue.2))
           end;
}


--For known cases, no branches are pruned, and therefore we just need
--   to map the hyp and var names
--Don't need the case broken into separate blocks because of this
function runKnownCase
IOVal<([String], ProofState)> ::=
   caseInfo::[[(ProofState, [AnyCommand])]] abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  return runKnownCase_help(flatMap(\ l -> l, caseInfo), abella,
            config, parsers, incomingState, allThms, keyRels,
            typeEnv, relEnv, constrEnv, ioin);
}
function runKnownCase_help
IOVal<([String], ProofState)> ::=
   caseInfo::[(ProofState, [AnyCommand])] abella::ProcessHandle
   config::Configuration parsers::AllParsers incomingState::ProofState
   allThms::[(QName, Metaterm)] keyRels::[QName]
   typeEnv::Env<TypeEnvItem> relEnv::Env<RelationEnvItem>
   constrEnv::Env<ConstructorEnvItem> ioin::IOToken
{
  --get commands and run them in Abella to get new proof state
  local run::IOVal<([String], ProofState)> =
      runCmds(head(caseInfo), allThms, incomingState, keyRels,
         typeEnv, relEnv, constrEnv, abella, config, parsers, ioin);

  --run it with the rest of the case
  local sub::IOVal<([String], ProofState)> =
      runKnownCase_help(tail(caseInfo), abella, config, parsers,
         run.iovalue.2, allThms, keyRels, typeEnv, relEnv,
         constrEnv, run.io);

  return
      case caseInfo of
      | [] -> ioval(ioin, ([], incomingState))
      | _::_ ->
        ioval(sub.io, (run.iovalue.1 ++ sub.iovalue.1, sub.iovalue.2))
      end;
}


--In preservability cases, each subgoal from the original may or may
--   not be present in the composition, as branches may prune.  Then
--   we need to check the current original state matches the current
--   composed state before using the commands.
function runPreservabilityCase
IOVal<([String], ProofState)> ::=
   preservabilityCase::[[(ProofState, [AnyCommand])]]
   abella::ProcessHandle config::Configuration parsers::AllParsers
   incomingState::ProofState allThms::[(QName, Metaterm)]
   keyRels::[QName] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   ioin::IOToken
{
  --get the mapping from old to new
  local unifyMap::ProofState = head(head(preservabilityCase)).1;
  unifyMap.mapTo = incomingState;
  unifyMap.typeEnv = typeEnv;
  unifyMap.relationEnv = relEnv;
  unifyMap.constructorEnv = constrEnv;

  --run the commands here
  local run::IOVal<([String], ProofState)> =
      foldl(\ rest::IOVal<([String], ProofState)>
              here::(ProofState, [AnyCommand]) ->
              let runThis::IOVal<([String], ProofState)> =
                  runCmds(here, allThms, rest.iovalue.2, keyRels,
                     typeEnv, relEnv, constrEnv, abella, config,
                     parsers, rest.io)
              in
                ioval(runThis.io,
                   (rest.iovalue.1 ++ runThis.iovalue.1,
                    runThis.iovalue.2))
              end,
            ioval(ioin, ([], incomingState)),
            head(preservabilityCase));

  --condition arguments to next bit on whether we run this part
  local nextState::ProofState =
      if unifyMap.mapSuccess then run.iovalue.2 else incomingState;
  local nextIO::IOToken =
      if unifyMap.mapSuccess then run.io else ioin;

  --run it with the rest of the case
  local sub::IOVal<([String], ProofState)> =
      runPreservabilityCase(tail(preservabilityCase), abella, config,
         parsers, nextState, allThms, keyRels, typeEnv, relEnv,
         constrEnv, nextIO);

  return
      case preservabilityCase of
      | [] -> ioval(ioin, ([], incomingState))
      | _::_ ->
        if unifyMap.mapSuccess
        then ioval(sub.io, (run.iovalue.1 ++ sub.iovalue.1,
                            sub.iovalue.2))
        else sub --skip this command as a pruned branch
      end;
}





--run the commands for a particular original proof state
function runCmds
IOVal<([String], ProofState)> ::= cmd::(ProofState, [AnyCommand])
   allThms::[(QName, Metaterm)] incomingState::ProofState
   keyRels::[QName] typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   abella::ProcessHandle config::Configuration parsers::AllParsers
   ioin::IOToken
{
  --get the mapping from old to new
  local unifyMap::ProofState = cmd.1;
  unifyMap.mapTo = incomingState;
  unifyMap.typeEnv = typeEnv;
  unifyMap.relationEnv = relEnv;
  unifyMap.constructorEnv = constrEnv;

  --get the commands
  local cmds::[ProofCommand] =
      flatMap(
         \ c::AnyCommand ->
           decorate c with {
              mapHyps = unifyMap.hypMap;
              mapVars = unifyMap.varMap;
              allThms = allThms;
              oldHyps =
                 unifyMap.extensibella:common:abstractSyntax:hypList;
              newHyps =
                 cmd.1.extensibella:common:abstractSyntax:hypList;
              keyRels = keyRels;
           }.mappedCmds,
         cmd.2);
  local cmdStrings::[String] = map((.abella_pp), cmds);

  local abellaOutput::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), cmds), abella, ioin, config);

  --send them to Abella and read the new proof state
  local newState::ProofState =
      fullStateProcessing(abellaOutput.iovalue, typeEnv,
         relEnv, constrEnv, parsers);

  return ioval(abellaOutput.io, (cmdStrings, newState));
}


--full processing for reading a proof state from Abella output, in
--   Extensibella but full names form
function fullStateProcessing
ProofState ::= stateStr::String typeEnv::Env<TypeEnvItem>
   relEnv::Env<RelationEnvItem> constrEnv::Env<ConstructorEnvItem>
   parsers::AllParsers
{
  local readState::ProofState =
      parsers.from_parse(stateStr,
         "<<Abella output>>").parseTree.ast.proof;
  local fromState::ProofState =
      decorate readState with {
         typeEnv = typeEnv;
         relationEnv = relEnv;
         constructorEnv = constrEnv;
      }.fromAbella;
  return decorate fromState with {
            typeEnv = typeEnv;
            relationEnv = relEnv;
            constructorEnv = constrEnv;
         }.full;
}
