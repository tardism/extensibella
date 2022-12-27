grammar extensibella:main;


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
   tyEnv::Env<TypeEnvItem>
   relationEnv::Env<RelationEnvItem>
   constructorEnv::Env<ConstructorEnvItem>
   stateList::[(Integer, ProverState)]
   config::Decorated CmdArgs
   abella::ProcessHandle ioin::IOToken
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  local debug::Boolean = currentProverState.debug;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  local any_a::AnyCommand = head(inputCommands);
  any_a.typeEnv = tyEnv;
  any_a.relationEnv = relationEnv;
  any_a.constructorEnv = constructorEnv;
  any_a.proverState = currentProverState;
  any_a.stateListIn = stateList;
  --whether we have something to send to Abella
  local speak_to_abella::Boolean =
      any(map((.isError), any_a.toAbellaMsgs)) &&
      !null(any_a.toAbella);
  --an error or message based on our own checking
  local our_own_output::String =
      errors_to_string(any_a.toAbellaMsgs);
  --Output if in debugging mode
  ----------------------------
  local debug_output::IOToken =
      if debug && config.showUser
      then printT(if speak_to_abella
                  then "Command sent:  " ++
                       implode("\n", (map((.pp), any_a.toAbella))) ++
                          "\n\n~~~~~~~~~~~~~~~~~~~~ End Sent ~~~~~~~~~~~~~~~~~~~~\n\n"
                  else "Nothing to send to Abella",
                  ioin)
      else ioin;


  {-
    PROCESS OUTPUT
  -}
  --Send to Abella and read output
  ----------------------------
  local back_from_abella::IOVal<String> =
      if speak_to_abella
      then sendCmdsToAbella(map((.pp), any_a.toAbella), abella,
                            debug_output, config)
      else ioval(debug_output, "");
  --Translate output
  ----------------------------
  local full_result::ParseResult<FullDisplay_c> =
      from_parse(back_from_abella.iovalue, "<<output>>");
  local full_a::FullDisplay =
      if !full_result.parseSuccess
      then error("Parse error in Abella output:\n\n" ++
                 back_from_abella.iovalue ++ "\n\n" ++
                 full_result.parseErrors)
      else full_result.parseTree.ast;
  any_a.newProofState = full_a.proof;
  --Clean up state
  ----------------------------
  local newProverState::ProverState = head(any_a.stateListOut).2;
  local shouldClean::Boolean =
      --check for errors from given commands
      full_result.parseSuccess && !full_a.isError &&
      --and if we have any cleaning things to do right now
      !null(newProverState.duringCommands) &&
      head(newProverState.duringCommands).1 ==
         full_a.proof.currentSubgoal;
  local cleanCommands::[ProofCommand] =
      head(newProverState.duringCommands).2;
  local cleaned::IOVal<String> =
      sendCmdsToAbella(map((.pp), cleanCommands), abella,
                       back_from_abella.io, config);
  local cleaned_display::FullDisplay =
      let p::ParseResult<FullDisplay_c> =
          from_parse(cleaned.iovalue, "<<output>>")
      in
        if shouldClean
        then if !p.parseSuccess
             then error("Parse error in Abella output:\n\n" ++
                        cleaned.iovalue ++ "\n\n" ++
                       p.parseErrors)
             else p.parseTree.ast
        else full_a
      end;
  local outputCleanCommands::IOToken =
      if shouldClean && debug && config.showUser
      then printT(implode("", map((.pp), cleanCommands)) ++
                  "\n\n~~~~~~~~~~~~~~~~~~~~ End Clean ~~~~~~~~~~~~~~~~~~~~\n\n",
                  cleaned.io)
      else cleaned.io;
  newProverState.replaceState = cleaned_display.proof;
  local cleanedStateList::[(Integer, ProverState)] =
      if shouldClean
      then (head(any_a.stateListOut).1 + length(cleanCommands),
            newProverState.replacedState)::tail(any_a.stateListOut)
      else any_a.stateListOut;
  --After Commands
  ----------------------------
  local cleanedProverState::ProverState = head(cleanedStateList).2;
  local afterCommands::[AnyCommand] =
      cleanedProverState.afterCommands;
  local runAfterCommands::Boolean =
      case cleanedProverState.state of
      | proofCompleted() -> !null(afterCommands)
      | _ -> false
      end;
  local aftered::IOVal<String> =
      sendCmdsToAbella(map((.pp), afterCommands), abella,
                       outputCleanCommands, config);
  local aftered_display::FullDisplay =
      let p::ParseResult<FullDisplay_c> =
          from_parse(aftered.iovalue, "<<output>>")
      in
        if runAfterCommands
        then if !p.parseSuccess
             then error("Parse error in Abella output:\n\n" ++
                        aftered.iovalue ++ "\n\n" ++
                        p.parseErrors)
             else p.parseTree.ast
        else cleaned_display
      end;
  local outputAfterCommands::IOToken =
      if runAfterCommands && debug && config.showUser
      then printT(implode("", map((.pp), afterCommands)) ++
                  "\n\n~~~~~~~~~~~~~~~~~~~~ End After ~~~~~~~~~~~~~~~~~~~~\n\n",
                  aftered.io)
      else aftered.io;
  local newStateList::[(Integer, ProverState)] =
      if runAfterCommands
      then (head(cleanedStateList).1 + length(afterCommands),
            proverState(cleanedProverState.state,
                        cleanedProverState.debug,
                        cleanedProverState.knownTheorems,
                        cleanedProverState.remainingObligations,
                        [], [], []))::tail(cleanedStateList)
      else cleanedStateList;
  --Process any imported theorems we can now add
  ----------------------------
  local handleIncoming::([AnyCommand], ProverState) =
      if head(newStateList).2.state.inProof
      then ([], head(newStateList).2)
      else handleIncomingThms(head(newStateList).2);
  local incomingCommands::[AnyCommand] = handleIncoming.1;
  local incominged::IOVal<String> = --assume this worked and don't parse
      sendCmdsToAbella(map((.pp), incomingCommands), abella,
                       outputAfterCommands, config);
  local outputIncomingThms::IOToken =
      if debug && config.showUser
      then printT(implode("\n", map((.pp), incomingCommands)) ++
                  "\n\n~~~~~~~~~~~~~~~~~~~~ End Incoming ~~~~~~~~~~~~~~~~~~~~\n\n",
                  incominged.io)
      else incominged.io;
  local completeStateList::[(Integer, ProverState)] =
      (head(newStateList).1 + length(handleIncoming.1),
       handleIncoming.2)::tail(newStateList);
  --Show to user
  ----------------------------
  local debug_back_output::IOToken =
      if debug && speak_to_abella && config.showUser
      then printT("******************** Read back from Abella: ********************\n\n" ++
                  aftered_display.pp ++ "\n\n" ++
                  "********************** End Abella output ***********************\n\n\n",
                  outputIncomingThms)
      else outputIncomingThms;
  local output_output::String =
      if speak_to_abella
      then if shouldClean
           then cleaned_display.fromAbella.pp
           else full_a.fromAbella.pp ++ "\n"
      else our_own_output ++ state.fromAbella.pp ++ "\n";
  local printed_output::IOToken =
      if config.showUser
      then printT(output_output, debug_back_output)
      else debug_back_output;


  {-
    EXIT
  -}
  --We can't use our normal send/read function because that looks for
  --a new prompt at the end, and we won't have any
  local exit_out_to_abella::IOToken =
      sendToProcess(abella, implode("\n", map((.pp), any_a.toAbella)),
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


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
               --use unsafeTrace to force it to print output
      run_step(tail(unsafeTrace(inputCommands, printed_output)),
               filename, from_parse,
               tyEnv, relationEnv, constructorEnv, --need to be updated
               completeStateList, config,
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
       then ioval(exit_message, 0)
       else if config.runningFile --running file should end on error
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
