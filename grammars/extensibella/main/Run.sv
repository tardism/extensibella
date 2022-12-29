grammar extensibella:main;


type StateList = [(Integer, ProverState)];
type Configuration = Decorated CmdArgs;


{--
  - Walk through a list of commands, processing the proofs they represent
  -
  - @inputCommands  The list of commands through which to walk
  - @filename  The name of the file we are processing, if any
  - @tyEnv  The types we know, both in the language ond defined in proof files
  - @relationEnv  The relations we know, both in the language and defined in proof files
  - @constructorEnv  The constructors we know, both in the language and defined in proof files
  - @statelist  The state of the prover after each command issued to the prover.
  -             The current state of the prover is the first element of the list.
  - @config  The configuration of the process
  - @abella  The process in which Abella is running
  - @ioin  The incoming IO token
  - @return  The resulting IO token and exit status
-}
function run_step
IOVal<Integer> ::=
   inputCommands::[AnyCommand]
   filename::String
   from_parse::Parser<FullDisplay_c>
   currentModule::QName
   tyEnv::Env<TypeEnvItem>
   relationEnv::Env<RelationEnvItem>
   constructorEnv::Env<ConstructorEnvItem>
   stateList::StateList
   config::Configuration
   abella::ProcessHandle ioin::IOToken
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  local debug::Boolean = currentProverState.debug;

  state.typeEnv = tyEnv;
  state.relationEnv = relationEnv;
  state.constructorEnv = constructorEnv;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  local any_a::AnyCommand = head(inputCommands);
  any_a.currentModule = currentModule;
  any_a.typeEnv = tyEnv;
  any_a.relationEnv = relationEnv;
  any_a.constructorEnv = constructorEnv;
  any_a.proverState = currentProverState;
  any_a.boundNames = state.usedNames;
  any_a.stateListIn = stateList;
  --whether we have something to send to Abella
  local speak_to_abella::Boolean =
      !any(map((.isError), any_a.toAbellaMsgs)) &&
      !null(any_a.toAbella);
  --an error or message based on our own checking
  local our_own_output::String =
      errors_to_string(any_a.toAbellaMsgs);
  --Send to Abella and read output
  ----------------------------
  local back_from_abella::IOVal<String> =
      if speak_to_abella
      then sendCmdsToAbella(map((.abella_pp), any_a.toAbella), abella,
                            ioin, config)
      else ioval(debug_output, "");
  local full_a::FullDisplay =
      processDisplay(back_from_abella.iovalue, from_parse);
  any_a.newProofState = full_a.proof;
  --Output if in debugging mode
  ----------------------------
  local debug_output::IOToken =
      if speak_to_abella
      then debugOutput(debug, config, any_a.toAbella,
              "Entered Command", back_from_abella.iovalue,
              back_from_abella.io)
      else debugOutput(debug, config, tail([anyParseFailure("")]),
              "Entered Command", "", ioin);


  {-
    FURTHER STATE PROCESSING
  -}
  --Clear any subgoals not needed to be proven in this module
  ----------------------------
  local cleared::IOVal<(StateList, FullDisplay)> =
      clearExtraSubgoals(any_a.stateListOut, full_a, from_parse,
                         debug_output, abella, debug, config);
  --After-proof commands
  ----------------------------
  local aftered::IOVal<StateList> =
      runAfterProofCommands(cleared.iovalue.1, cleared.io, abella,
                            debug, config);
  --Process any imported theorems we can now add
  ----------------------------
  local incominged::IOVal<StateList> =
      runIncoming(aftered.iovalue, aftered.io, abella, debug, config);
  --Show to user
  ----------------------------
  local finalDisplay::FullDisplay = cleared.iovalue.2;
  finalDisplay.typeEnv = tyEnv;
  finalDisplay.relationEnv = relationEnv;
  finalDisplay.constructorEnv = constructorEnv;
  local output_output::String =
      if speak_to_abella
      then finalDisplay.fromAbella.pp ++ "\n"
      else our_own_output ++ state.fromAbella.pp ++ "\n";
  local printed_output::IOToken =
      if config.showUser
      then printT(output_output, incominged.io)
      else incominged.io;


  {-
    EXIT
  -}
  local exited::IOToken =
      exitAbella(any_a.toAbella, ioin, abella, debug, config);


  {-
    RUN REPL AGAIN
  -}
  local newTys::Env<TypeEnvItem> =
      if full_a.isError
      then tyEnv
      else addEnv(tyEnv, any_a.tys);
  local newRels::Env<RelationEnvItem> =
      if full_a.isError
      then relationEnv
      else addEnv(relationEnv, any_a.rels);
  local newConstrs::Env<ConstructorEnvItem> =
      if full_a.isError
      then constructorEnv
      else addEnv(constructorEnv, any_a.constrs);
  local again::IOVal<Integer> =
               --use unsafeTrace to force it to print output
      run_step(tail(unsafeTrace(inputCommands, printed_output)),
               filename, from_parse, currentModule,
               newTys, newRels, newConstrs,
               incominged.iovalue, config,
               abella, printed_output);


  return
     case inputCommands of
     | [] ->
       if config.runningFile
       then if state.inProof
            then ioval(printT("Proof in progress at end of file " ++
                              filename ++ "\n", ioin), 1)
            else if !null(head(stateList).2.remainingObligations)
            then ioval(printT("Not all proof obligations fulfilled" ++
                              " in file " ++ filename ++ "\n", ioin),
                       1)
            else ioval(printT("Successfully processed file " ++
                              filename ++ "\n", ioin), 0)
       else ioval(ioin, 0)
     | _::tl ->
       if any_a.isQuit
       then ioval(exited, 0)
       else if config.runningFile --running file should not error
            then if any(map((.isError), any_a.toAbellaMsgs))
                 then ioval(printT("Could not process full file " ++
                                   filename ++ ":\n" ++
                                   our_own_output ++ "\n",
                                   back_from_abella.io),
                            1)
                 else if full_a.isError
                 then ioval(printT("Could not process full file " ++
                                   filename ++ ":\n" ++ full_a.pp,
                                   back_from_abella.io), 1)
                 else again
            else again
     end;
}




--Clear any extra subgoals Abella shows but this module doesn't need
--to prove
function clearExtraSubgoals
IOVal<(StateList, FullDisplay)> ::=
   stateListIn::StateList displayIn::FullDisplay
   from_parse::Parser<FullDisplay_c> ioin::IOToken
   abella::ProcessHandle debug::Boolean config::Configuration
{
  local initProverState::ProverState = head(stateListIn).2;
  local shouldClean::Boolean =
      --check for errors from given commands
      !displayIn.isError &&
      --and if we have any cleaning things to do right now
      !null(initProverState.duringCommands) &&
      head(initProverState.duringCommands).1 ==
         displayIn.proof.currentSubgoal;
  local cleanCommands::[ProofCommand] =
      if shouldClean then head(initProverState.duringCommands).2
                     else [];
  local cleaned::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), cleanCommands), abella,
                       ioin, config);
  local cleaned_display::FullDisplay =
      processDisplay(cleaned.iovalue, from_parse);
  local outputCleanCommands::IOToken =
      if shouldClean
      then debugOutput(debug, config, cleanCommands,
              "Clear Extra Subgoals", cleaned.iovalue, cleaned.io)
      else debugOutput(debug, config, cleanCommands,
              "Clear Extra Subgoals", "", ioin);
  local cleanedStateList::StateList =
      (head(stateListIn).1 + length(cleanCommands),
       proverState(cleaned_display.proof,
          initProverState.debug,
          initProverState.knownTheorems,
          initProverState.remainingObligations,
          initProverState.provingThms,
          tail(initProverState.duringCommands), --drop used first set
          initProverState.afterCommands))::tail(stateListIn);
  return ioval(outputCleanCommands,
               if shouldClean
               then (cleanedStateList, cleaned_display)
               else (stateListIn, displayIn));
}


--Once a proof is done to Abella's satisfaction, do the after-proof
--commands needed for it
function runAfterProofCommands
IOVal<StateList> ::=
   stateListIn::StateList ioin::IOToken abella::ProcessHandle
   debug::Boolean config::Configuration
{
  local initProverState::ProverState = head(stateListIn).2;
  local runAfterCommands::Boolean =
      case initProverState.state of
      | proofCompleted() -> !null(initProverState.afterCommands)
      | _ -> false
      end;
  local afterCommands::[AnyCommand] =
      if runAfterCommands then initProverState.afterCommands else [];
  local aftered::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), afterCommands), abella,
                       ioin, config);
  --don't parse aftered.iovalue---assume it worked
  local outputAfterCommands::IOToken =
      if runAfterCommands
      then debugOutput(debug, config, afterCommands,
              "After-Proof Commands", aftered.iovalue, aftered.io)
      else debugOutput(debug, config, afterCommands,
              "After-Proof Commands", "", ioin);
  local newStateList::StateList =
      (head(stateListIn).1 + length(afterCommands),
       proverState(initProverState.state,
                   initProverState.debug,
                   initProverState.knownTheorems,
                   initProverState.remainingObligations,
                   [], [], []))::tail(stateListIn);
  return ioval(outputAfterCommands,
               if runAfterCommands
               then newStateList
               else stateListIn);
}


--If the proof is done, pass through any imported proof pieces that
--can now be done
function runIncoming
IOVal<StateList> ::=
   stateListIn::StateList ioin::IOToken abella::ProcessHandle
   debug::Boolean config::Configuration
{
  local handleIncoming::([AnyCommand], ProverState) =
      if head(stateListIn).2.state.inProof
      then ([], head(stateListIn).2)
      else handleIncomingThms(head(stateListIn).2);
  local incomingCommands::[AnyCommand] = handleIncoming.1;
  local incominged::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), incomingCommands), abella,
                       ioin, config);
  --don't parse incominged.iovalue---assume it worked
  local outputIncomingThms::IOToken =
      if !null(incomingCommands)
      then debugOutput(debug, config, incomingCommands,
              "Imported Theorems", incominged.iovalue, incominged.io)
      else debugOutput(debug, config, incomingCommands,
              "ImportedTheorems", "", ioin);
  local completeStateList::[(Integer, ProverState)] =
      (head(stateListIn).1 + length(handleIncoming.1),
       handleIncoming.2)::tail(stateListIn);
  return ioval(outputIncomingThms,
               if !null(incomingCommands)
               then completeStateList
               else stateListIn);
}


--Handle Abella exiting
function exitAbella
IOToken ::= commands::[AnyCommand] ioin::IOToken abella::ProcessHandle
            debug::Boolean config::Configuration
{
  local debug_output::IOToken =
      debugOutput(debug, config, commands, "User Commands",
                  "No Abella output because quitting", ioin);
  --We can't use our normal send/read function because that looks for
  --a new prompt at the end, and we won't have any
  local exit_out_to_abella::IOToken =
      sendToProcess(abella,
                    implode("\n", map((.abella_pp), commands)),
                    debug_output);
  local wait_on_exit::IOToken =
      waitForProcess(abella, exit_out_to_abella);
  --Guaranteed to get all the output because we waited for the process
  --to exit first
  local any_last_words::IOVal<String> =
      readAllFromProcess(abella, wait_on_exit);
  local output_last::IOToken =
      if config.showUser
      then printT(any_last_words.iovalue, any_last_words.io)
      else any_last_words.io;
  local exit_message::IOToken =
      if config.showUser
      then printT("Quitting.\n", output_last)
      else output_last;
  return exit_message;
}


--Parse a FullDisplay out of the string
--Assumes it succeeds, but gives a helpful error if it doesn't
function processDisplay
FullDisplay ::= s::String from_parse::Parser<FullDisplay_c>
{
  local p::ParseResult<FullDisplay_c> =
      from_parse(s, "<<Abella output>>");
  return if p.parseSuccess
         then p.parseTree.ast
         else error("Parse error in Abella output:\n\n" ++
                    s ++ "\n\n" ++ p.parseErrors);
}


--Display debugging output to the user, if you should
--commandReason is to explain whence the commands came
--   (e.g. after-theorem commands)
function debugOutput
attribute abella_pp {} occurs on command =>
IOToken ::= debug::Boolean config::Configuration commands::[command]
            commandReason::String abellaOutput::String ioin::IOToken
{
  local startString::String =
      "\n~~~~~~~~~~~~~~~~~~~~ Start " ++ commandReason ++
       " ~~~~~~~~~~~~~~~~~~~~\n\n";
  local commandString::String =
      if null(commands)
      then "<<< No Commands >>>"
      else implode("", map((.abella_pp), commands));
  local abellaString::String =
      "\n***** Abella Output *****\n" ++ abellaOutput;
  local endString::String =
      "\n\n~~~~~~~~~~~~~~~~~~~~ End " ++ commandReason ++
         " ~~~~~~~~~~~~~~~~~~~~\n\n";
  local full::String =
      startString ++ commandString ++
      (if null(commands) then "" else abellaString) ++
      endString;
  return if debug && config.showUser
         then printT(full, ioin)
         else ioin;
}
