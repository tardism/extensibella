grammar extensibella:main;


type StateList = [(Integer, ProverState)];
type Configuration = Decorated CmdArgs;


{--
 - Set up and walk through a list of commands, presenting the proofs they represent
 -
 - @filename  The name of the file we are processing, if any
 - @cmds  Commands being processed
 - @import_parse  Parser for reading imported files
 - @from_parse  Parser for reading Abella output
 - @currentModule  Module about which we are proving properties
 - @definitionCmds  Commands for imports
 - @importDefs  Proof definitions being imported
 - @importThms  Proof obligations being imported
 - @config  The configuration of the process
 - @ioin  The incoming IO token
 - @return  The resulting IO token and exit status
-}
function run
IOVal<Integer> ::=
   filename::String cmds::[AnyCommand]
   import_parse::Parser<ListOfCommands_c>
   from_parse::Parser<FullDisplay_c>
   currentModule::QName
   definitionCmds::ListOfCommands
   importDefs::[DefElement]
   importThms::[ThmElement]
   config::Configuration ioin::IOToken
{
  local started::IOVal<Either<String ProcessHandle>> =
      startAbella(ioin, config);
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(import_parse, started.io);
  --basic context information from the definition file
  local build_context::IOVal<(Env<TypeEnvItem>, Env<RelationEnvItem>,
                              Env<ConstructorEnvItem>)> =
      set_up_abella_module(currentModule, definitionCmds, importDefs,
         from_parse, started.iovalue.fromRight, stdLibThms.io,
         config);
  --context information for imported definitions
  local importedProofDefs::([TypeEnvItem], [RelationEnvItem],
                            [ConstructorEnvItem]) =
      defElementsDefinitions(importDefs);
  --combine definition file and imported proof definitions
  local startProverState::ProverState =
      defaultProverState(importThms,
         addEnv(build_context.iovalue.1, importedProofDefs.1),
         addEnv(build_context.iovalue.2, importedProofDefs.2),
         addEnv(build_context.iovalue.3, importedProofDefs.3),
         stdLibThms.iovalue.fromRight);
  --
  local handleIncoming::([AnyCommand], ProverState) =
      handleIncomingThms(startProverState);
  local sendIncoming::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), handleIncoming.1),
         started.iovalue.fromRight, build_context.io, config);

  return
     if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else if !stdLibThms.iovalue.isRight
     then ioval(printT("Error:  " ++ stdLibThms.iovalue.fromLeft ++
                       "\n", stdLibThms.io), 1)
     else run_step(cmds, filename, from_parse, currentModule,
             [(-1, handleIncoming.2)], config,
             started.iovalue.fromRight, sendIncoming.io);
}


{--
 - Walk through a list of commands, processing the proofs they represent
 -
 - @inputCommands  The list of commands through which to walk
 - @filename  The name of the file we are processing, if any
 - @from_parse  Parser for reading Abella output
 - @currentModule  Module about which we are proving properties
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
   stateList::StateList
   config::Configuration
   abella::ProcessHandle ioin::IOToken
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  local debug::Boolean = currentProverState.debug;

  state.typeEnv = currentProverState.knownTypes;
  state.relationEnv = currentProverState.knownRels;
  state.constructorEnv = currentProverState.knownConstrs;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  local any_a::AnyCommand = head(inputCommands);
  any_a.currentModule = currentModule;
  any_a.typeEnv = currentProverState.knownTypes;
  any_a.relationEnv = currentProverState.knownRels;
  any_a.constructorEnv = currentProverState.knownConstrs;
  any_a.proverState = currentProverState;
  any_a.boundNames = state.usedNames;
  any_a.stateListIn = stateList;
  --whether we have an error
  local is_error::Boolean = any(map((.isError), any_a.toAbellaMsgs));
  --whether we have something to send to Abella
  local speak_to_abella::Boolean =
      !is_error && !null(any_a.toAbella);
  --an error or message based on our own checking
  local our_own_output::String =
      errors_to_string(any_a.toAbellaMsgs);
  --Send to Abella and read output
  ----------------------------
  local back_from_abella::IOVal<String> =
      if speak_to_abella
      then sendCmdsToAbella(map((.abella_pp), any_a.toAbella), abella,
                            ioin, config)
      else ioval(ioin, "");
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
                                    --Why?  Solving type constraints
      else debugOutput(debug, config, tail([anyParseFailure("")]),
              "Entered Command", "", ioin);


  {-
    FURTHER STATE PROCESSING
  -}
  --Run any during commands for the current subgoal
  ----------------------------
  local duringed::IOVal<(StateList, FullDisplay)> =
      runDuringCommands(any_a.stateListOut, full_a, from_parse,
                        debug_output, abella, debug, config);
  --After-proof commands
  ----------------------------
  local aftered::IOVal<StateList> =
      runAfterProofCommands(duringed.iovalue.1, duringed.io, abella,
                            debug, config);
  --Process any imported theorems we can now add
  ----------------------------
  local incominged::IOVal<StateList> =
      runIncoming(aftered.iovalue, aftered.io, abella, debug, config);
  local nonErrorStateList::StateList = incominged.iovalue;
  --Show to user
  ----------------------------
  local finalDisplay::FullDisplay = duringed.iovalue.2;
  finalDisplay.typeEnv = head(nonErrorStateList).2.knownTypes;
  finalDisplay.relationEnv = head(nonErrorStateList).2.knownRels;
  finalDisplay.constructorEnv =
      head(nonErrorStateList).2.knownConstrs;
  local output_output::String =
      if speak_to_abella
      then finalDisplay.fromAbella.pp ++ "\n"
      else our_own_output ++ state.fromAbella.pp ++ "\n";
  local printed_output::IOToken =
      if config.showUser
      then printT(output_output, incominged.io)
      else incominged.io;


  {-
    ANNOTATED FILE
  -}
  local annotated_output::IOToken =
      if config.outputAnnotated
      then appendFileT(config.annotatedFile,
              --create block
              "<pre class=\"code\">\n" ++
                --add prompt and command
                " < <b>" ++ stripExternalWhiteSpace(any_a.pp) ++
                   "</b>\n\n" ++
                --Extensibella output
                stripExternalWhiteSpace(output_output) ++ "\n" ++
              --end block
              "</pre>\n",
              printed_output)
      else printed_output;


  {-
    EXIT
  -}
  local exited::IOToken =
      exitAbella(any_a.toAbella, ioin, abella, debug, config);


  {-
    RUN REPL AGAIN
  -}
  local finalStateList::StateList =
      if speak_to_abella
      then nonErrorStateList
      else if is_error
      then stateList
      else any_a.stateListOut;
  local again::IOVal<Integer> =
               --use unsafeTrace to force it to print output
      run_step(tail(unsafeTrace(inputCommands, annotated_output)),
               filename, from_parse, currentModule,
               finalStateList, config,
               abella, annotated_output);


  return
     case inputCommands of
     | [] ->
       if !config.runningFile
       then ioval(ioin, 0)
       else if state.inProof
       then ioval(printT("Proof in progress at end of file " ++
                         filename ++ "\n", ioin), 1)
       else if !null(head(stateList).2.remainingObligations)
       then ioval(printT("Not all proof obligations fulfilled" ++
                         " in file " ++ filename ++ "\n", ioin), 1)
       else ioval(printT("Successfully processed file " ++
                         filename ++ "\n", ioin), 0)
     --File-specific considerations
     | _::tl when config.runningFile ->
       if is_error
       then ioval(printT("Could not process full file " ++ filename ++
                         ":\n" ++ our_own_output ++ "\n",
                         back_from_abella.io), 1)
       else if full_a.isError
       then ioval(printT("Could not process full file " ++ filename ++
                         ":\n" ++ full_a.pp, back_from_abella.io), 1)
       else if any_a.isQuit && !null(tl)
       then ioval(printT("Warning:  File contains Quit before end\n",
                         back_from_abella.io), 1)
       else again
     --Interactive-specific considerations
     | _::tl ->
       if any_a.isQuit
       then ioval(exited, 0)
       else if null(any_a.stateListOut) --full undo in PG
       then expect_quit("Error:  After full undo, must have a Quit" ++
                        " command to finish", debug_output)
       else again
     end;
}




--Run any during commands that apply at this subgoal
function runDuringCommands
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
      case initProverState.duringCommands of
      | [] -> false
      | (sg, _)::_ -> sg == displayIn.proof.currentSubgoal
      end;
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
              "Run During Commands", cleaned.iovalue, cleaned.io)
      else debugOutput(debug, config, cleanCommands,
              "Run During Commands", "", ioin);
  local cleanedStateList::StateList =
      (head(stateListIn).1 + length(cleanCommands),
       dropDuringCommand(setProofState(initProverState,
                            cleaned_display.proof))
      )::tail(stateListIn);
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
  local proofDone::Boolean =
      case initProverState.state of
      | proofCompleted() -> true
      | _ -> false
      end;
  local runAfterCommands::Boolean =
      proofDone && !null(initProverState.afterCommands);
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

  --Put it together
  local newStateList::StateList =
      (head(stateListIn).1 +
       if runAfterCommands then length(afterCommands) else 0,
       finishProof(initProverState))::tail(stateListIn);
  return ioval(if runAfterCommands then outputAfterCommands else ioin,
               if proofDone then newStateList else stateListIn);
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
              "Imported Theorems", "", ioin);
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
