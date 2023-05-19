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
   filename::String cmds::ListOfCommands
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

  --set inh attrs for processing file
  cmds.currentModule = currentModule;
  cmds.filename = filename;
  cmds.from_parse = from_parse;
  cmds.stateList = [(-1, handleIncoming.2)];
  cmds.config = config;
  cmds.abella = started.iovalue.fromRight;
  cmds.ioin = sendIncoming.io;

  return
     if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else if !stdLibThms.iovalue.isRight
     then ioval(printT("Error:  " ++ stdLibThms.iovalue.fromLeft ++
                       "\n", stdLibThms.io), 1)
     else cmds.runResult;
}




inherited attribute filename::String;
inherited attribute from_parse::Parser<FullDisplay_c>;
inherited attribute stateList::StateList;
inherited attribute config::Configuration;
inherited attribute abella::ProcessHandle;
inherited attribute ioin::IOToken;

synthesized attribute runResult::IOVal<Integer>;

synthesized attribute isNull::Boolean;

attribute
   filename, from_parse, stateList, config, abella, ioin, runResult,
   isNull
occurs on ListOfCommands;
propagate filename, from_parse, config, abella on ListOfCommands;


aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.isNull = true;

  local currentProverState::ProverState = head(top.stateList).snd;
  local state::ProofState = currentProverState.state;

  --Permit the addition of extra actions to be carried out
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;

  local finalIO::IOToken = io(top.ioin);
  top.runResult =
      if !top.config.runningFile --non-file can quit whenever
      then ioval(finalIO, 0)
      else if state.inProof
      then ioval(printT("Proof in progress at end of file " ++
                        top.filename ++ "\n", finalIO), 1)
      else if !null(head(top.stateList).2.remainingObligations)
      then ioval(printT("Not all proof obligations fulfilled in " ++
                        "file " ++ top.filename ++ "\n", finalIO), 1)
      else ioval(printT("Successfully processed file " ++
                        top.filename ++ "\n", finalIO), 0);
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.isNull = false;

  local currentProverState::ProverState = head(top.stateList).snd;
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
  --we need a copy because we need to set the envs differently here
  --than for imports that also use ListOfCommands
  local any_a::AnyCommand = a;
  any_a.currentModule = top.currentModule;
  any_a.typeEnv = currentProverState.knownTypes;
  any_a.relationEnv = currentProverState.knownRels;
  any_a.constructorEnv = currentProverState.knownConstrs;
  any_a.proverState = currentProverState;
  any_a.boundNames = state.usedNames;
  any_a.stateListIn = top.stateList;
  --whether we have an error
  local is_error::Boolean = any(map((.isError), any_a.toAbellaMsgs));
  local speak_to_abella::Boolean = !is_error && !null(any_a.toAbella);
  --an error or message based on our own checking
  local our_own_output::String = errors_to_string(any_a.toAbellaMsgs);
  --Send to Abella and read output
  ----------------------------
  local io_action_1::IOVal<String> =
      if speak_to_abella
      then sendCmdsToAbella(map((.abella_pp), any_a.toAbella),
              top.abella, top.ioin, top.config)
      else ioval(top.ioin, "");
  local back_from_abella::String = io_action_1.iovalue;
  local full_a::FullDisplay =
      processDisplay(back_from_abella, top.from_parse);
  any_a.newProofState = full_a.proof;
  --Output if in debugging mode
  ----------------------------
  local io_action_2::IOToken =
      if speak_to_abella
      then debugOutput(debug, top.config, any_a.toAbella,
              "Entered Command", back_from_abella, io_action_1.io)
                                      --Why?  Solving type constraints
      else debugOutput(debug, top.config, tail([anyParseFailure("")]),
              "Entered Command", "", io_action_1.io);

  {-
    FURTHER STATE PROCESSING
  -}
  --whether to do the processing or launder the IOToken through
  local continueProcessing::Boolean =
      speak_to_abella && !is_error && !null(any_a.stateListOut);
  --Run any during commands for the current subgoal
  local io_action_3::IOVal<(StateList, FullDisplay)> =
      if continueProcessing
      then runDuringCommands(any_a.stateListOut, full_a, top.from_parse,
              io_action_2, top.abella, debug, top.config)
      else ioval(io_action_2, error("Should not access (3)"));
  local duringed::(StateList, FullDisplay) = io_action_3.iovalue;
  --After-proof commands
  local io_action_4::IOVal<StateList> =
      if continueProcessing
      then runAfterProofCommands(duringed.1, io_action_3.io,
              top.abella, debug, top.config)
      else ioval(io_action_3.io, error("Should not access (4)"));
  local aftered::StateList = io_action_4.iovalue;
  --Process any imported theorems we can now add
  local io_action_5::IOVal<StateList> =
      if continueProcessing
      then runIncoming(aftered, io_action_4.io, top.abella,
                       debug, top.config)
      else ioval(io_action_4.io, error("Should not access (5)"));
  local nonErrorStateList::StateList = io_action_5.iovalue;
  local nonErrorProverState::ProverState = head(nonErrorStateList).2;
  --Show to user
  ----------------------------
  local finalDisplay::FullDisplay = duringed.2;
  finalDisplay.typeEnv = nonErrorProverState.knownTypes;
  finalDisplay.relationEnv = nonErrorProverState.knownRels;
  finalDisplay.constructorEnv = nonErrorProverState.knownConstrs;
  local output_output::String =
      if speak_to_abella && continueProcessing
      then showDoc(80, finalDisplay.fromAbella.pp) ++ "\n"
      else our_own_output ++ showDoc(80, state.fromAbella.pp) ++ "\n";
  local io_action_6::IOToken =
      if top.config.showUser
      then printT(output_output, io_action_5.io)
      else io_action_5.io;

  {-
    EXIT
  -}
  --this is outside the io_action numbering scheme because it doesn't
  --strictly happen in sync with the rest of them
  local exited::IOToken = exitAbella(any_a.toAbella, top.ioin,
                                     top.abella, debug, top.config);


  --Permit the addition of extra actions to be carried out after the
  --processing above
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;

  --Annotated HTML file with command and non-dying output
  io <- \ i::IOToken ->
          if top.config.outputAnnotated
          then appendFileT(top.config.annotatedFile,
                  --create block
                  "<pre class=\"code\">\n" ++
                    --add prompt and command
                    " < <b>" ++ stripExternalWhiteSpace(
                                   showDoc(80, nest(3, any_a.pp))) ++
                       "</b>\n\n" ++
                    --Extensibella output
                    stripExternalWhiteSpace(output_output) ++ "\n" ++
                  --end block
                  "</pre>\n",
                  i)
          else i;

  --finalIO is the IOToken for all this command's IO being done,
  --including any extra actions added apart from the basic sequence
  local finalIO::IOToken =
      io(if any_a.isQuit then exited else io_action_6);

  rest.ioin = finalIO;
  rest.stateList =
       if speak_to_abella
       then nonErrorStateList
       else if is_error
       then top.stateList
       else any_a.stateListOut;

  top.runResult =
      if top.config.runningFile
      then if is_error
           then ioval(printT("Could not process full file " ++
                         top.filename ++ ":\n" ++ our_own_output ++
                         "\n", finalIO), 1)
           else if full_a.isError
           then ioval(printT("Could not process full file " ++
                             top.filename ++ ":\n" ++
                             showDoc(80, full_a.pp),
                         finalIO), 1)
           else if any_a.isQuit && !rest.isNull
           then ioval(printT("Warning:  File contains Quit before " ++
                             "end\n", finalIO), 1)
           else rest.runResult
      else if any_a.isQuit
           then ioval(finalIO, 0)
           else if !is_error &&
                   null(any_a.stateListOut) --full undo in PG
           then expect_quit("Error:  After full undo, must have a " ++
                   "Quit command to finish", finalIO)
               --use unsafeTrace to force it to print output
           else unsafeTrace(rest.runResult, finalIO);
}



--Combine two IO actions into one
function combineIO
(IOToken ::= IOToken) ::= first::(IOToken ::= IOToken)
                          second::(IOToken ::= IOToken)
{
  return \ i::IOToken -> second(first(i));
}





{-
  Functions assisting in checking a file
-}

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
