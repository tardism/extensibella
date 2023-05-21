grammar extensibella:main:run;

imports silver:util:subprocess;

--Either start Abella or fail with an error message
function startAbella
IOVal<Either<String ProcessHandle>> ::=
      ioin::IOToken config::Decorated CmdArgs
{
  local stdLibFiles::IOVal<Either<String [String]>> =
      standardLibraryFiles(ioin);
  local importStrings::[String] =
      map(\ filename::String -> "Import \"" ++ filename ++ "\".",
          stdLibFiles.iovalue.fromRight);
  local library_cmds::[String] =
      ["Kind $lib__bool   type.",
       "Kind $lib__nat    type.",
       "Kind $lib__pair   type -> type -> type."] ++
      importStrings;

  local abella::IOVal<ProcessHandle> =
      spawnProcess("abella", [], stdLibFiles.io);
  --Read Abella's welcome message
  local abella_initial_string::IOVal<String> =
      read_abella_output(abella.iovalue, abella.io);
  --Send the library imports to Abella
  local send_imports::IOVal<String> =
      sendCmdsToAbella(library_cmds, abella.iovalue,
                       abella_initial_string.io, config);

  return
     case stdLibFiles.iovalue of
     | left(err) -> ioval(stdLibFiles.io, left(err))
     | right(_) -> ioval(send_imports.io, right(abella.iovalue))
     end;
}



--Send the commands from importing module specifications and build
--   the environments
function set_up_abella_module
IOVal<(Env<TypeEnvItem>, Env<RelationEnvItem>,
       Env<ConstructorEnvItem>)> ::=
     currentModule::QName comms::ListOfCommands defs::[DefElement]
     parsers::AllParsers abella::ProcessHandle ioin::IOToken
     config::Decorated CmdArgs
{
  local sendToAbella::[String] =
      map((.abella_pp), comms.commandList) ++
      map((.abella_pp), flatMap((.encode), defs));
  local back::IOVal<String> =
      sendCmdsToAbella(sendToAbella, abella, ioin, config);
  local parsedOutput::ParseResult<FullDisplay_c> =
      parsers.from_parse(back.iovalue, "<<output>>");

  --nothing is known going into this
  comms.typeEnv = [];
  comms.relationEnv = [];
  comms.constructorEnv = [];
  comms.currentModule = error("currentModule not needed?");

  return
     if !parsedOutput.parseSuccess
     then error("Could not parse Abella output:\n\n" ++
                back.iovalue ++ "\n\n" ++ parsedOutput.parseErrors)
     else if parsedOutput.parseTree.ast.isError
     then error("Error passing module specifications to Abella:\n" ++
                showDoc(80, parsedOutput.parseTree.ast.pp))
     else ioval(back.io,
                (buildEnv(comms.tys), buildEnv(comms.rels),
                 buildEnv(comms.constrs)));
}



--Send each of the given Abella commands to Abella in order
--Returns the output text of the last one
function sendCmdsToAbella
IOVal<String> ::= cmds::[String] abella::ProcessHandle ioin::IOToken
                  config::Decorated CmdArgs
{
  return
     case cmds of
     | [] -> ioval(ioin, "")
     | [c] -> sendCmdToAbella(c, abella, ioin, config)
     | c::tl ->
       sendCmdsToAbella(tl, abella,
                        sendCmdToAbella(c, abella, ioin, config).io,
                        config)
     end;
}

--Send a single command to Abella and get its output text back
function sendCmdToAbella
IOVal<String> ::= cmd::String abella::ProcessHandle ioin::IOToken
                  config::Decorated CmdArgs
{
  local sent::IOToken = sendToProcess(abella, cmd, ioin);
  local dumped::IOToken =
      if config.dumpAbella
      then appendFileT(config.dumpAbellaFile, cmd ++ "\n", sent)
      else sent;
  return read_abella_output(abella, dumped);
}


--Read the full Abella output (prompt-terminated) for one command
--Returns the text of the output
function read_abella_output
IOVal<String> ::= abella::ProcessHandle ioin::IOToken
{
  local read::IOVal<String> =
      readUntilFromProcess(abella, "< ", ioin);
  return ioval(read.io, removeLastWord(read.iovalue));
}

--Remove the last word in a string
--We use this because the Abella prompt has the form "name < ", which
--   is guaranteed to be the last thing in the given string.
function removeLastWord
String ::= str::String
{
  local space::Integer = lastIndexOf("\n", str);
  local noWord::String = substring(0, space, str);
  return if space >= 0 then noWord else "";
}


--Remove white space from the front and end
function stripExternalWhiteSpace 
String ::= str::String
{
  local split::[String] = explode("", str);
  local cleanedHead::[String] = removeInitialSpaces(split);
  local reversedList::[String] = reverse(cleanedHead);
  local cleanedTail::[String] = removeInitialSpaces(reversedList);
  local forwardList::[String] = reverse(cleanedTail);
  return implode("", forwardList);
}
--Helper---takes a list of single characters
function removeInitialSpaces
[String] ::= lst::[String]
{
  return
    case lst of
    | [] -> []
    | h::t ->
      if isSpace(h)
      then removeInitialSpaces(t)
      else lst
    end;
}
