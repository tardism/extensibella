grammar extensibella:main;


--Either start Abella or fail with an error message
function startAbella
IOVal<Either<String ProcessHandle>> ::= ioin::IOToken config::Decorated CmdArgs
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
      envVarT("EXTENSIBELLA_LIBRARY", ioin);
  local library_cmds::[String] =
      ["Kind $lib__bool   type.",
       "Import \"" ++ library_loc.iovalue ++ "bools\".",
       "Kind $lib__nat   type.",
       "Import \"" ++ library_loc.iovalue ++ "integer_addition\".",
       "Import \"" ++ library_loc.iovalue ++ "integer_multiplication\".",
       "Import \"" ++ library_loc.iovalue ++ "integer_division\".",
       "Import \"" ++ library_loc.iovalue ++ "integer_comparison\".",
       "Import \"" ++ library_loc.iovalue ++ "lists\".",
       "Import \"" ++ library_loc.iovalue ++ "strings\".",
       "Kind $lib__pair   type -> type -> type.",
       "Import \"" ++ library_loc.iovalue ++ "pairs\"."];

  local abella::IOVal<ProcessHandle> =
      spawnProcess("abella", [], library_loc.io);
  --Read Abella's outputs from the library imports, in addition to the
  --   welcome message
  local abella_initial_string::IOVal<String> =
      read_abella_output(abella.iovalue, abella.io);
  --Send the library imports to Abella
  local send_imports::IOVal<String> =
      sendCmdsToAbella(library_cmds, abella.iovalue,
                       abella_initial_string.io, config);

  return
     if library_loc.iovalue == ""
     then ioval(library_loc.io,
                left("Interface library location not set; " ++
                     "must run through given script"))
     else ioval(send_imports.io, right(abella.iovalue));
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
