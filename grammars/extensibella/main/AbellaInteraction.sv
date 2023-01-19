grammar extensibella:main;


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


function importStdLibThms
IOVal<Either<String [(QName, Metaterm)]>> ::=
      import_parse::Parser<ListOfCommands_c> ioin::IOToken
{
  local stdLibFiles::IOVal<Either<String [String]>> =
      standardLibraryFiles(ioin);
  local read::IOVal<Either<String [(QName, Metaterm)]>> =
      readStdLibThms(stdLibFiles.iovalue.fromRight, import_parse,
                     stdLibFiles.io);
  return
     case stdLibFiles.iovalue of
     | left(err) -> ioval(stdLibFiles.io, left(err))
     | right(_) -> ioval(read.io, read.iovalue)
     end;
}

function readStdLibThms
IOVal<Either<String [(QName, Metaterm)]>> ::=
      filenames::[String] import_parse::Parser<ListOfCommands_c>
      ioin::IOToken
{
  local contents::IOVal<String> =
      readFileT(head(filenames) ++ ".thm", ioin);
  local parsed::ParseResult<ListOfCommands_c> =
      import_parse(contents.iovalue, head(filenames) ++ ".thm");
  local ast::ListOfCommands = parsed.parseTree.ast;
  ast.currentModule = toQName("extensibella:stdLib");
  ast.proverState = error("proverState not needed");
  local again::IOVal<Either<String [(QName, Metaterm)]>> =
      readStdLibThms(tail(filenames), import_parse, contents.io);
  return
     case filenames of
     | [] -> ioval(ioin, right([]))
     | f::_ when !parsed.parseSuccess ->
       ioval(contents.io,
             left("Could not parse file " ++ f ++ ".thm:\n" ++
                  parsed.parseErrors))
     | _::_ when again.iovalue.isLeft ->
       ioval(again.io, again.iovalue)
     | _::_ ->
       ioval(again.io,
             right(ast.declaredThms ++ again.iovalue.fromRight))
     end;
}


--Find all the library files, with their full path
--Does not include file extensions
function standardLibraryFiles
IOVal<Either<String [String]>> ::= ioin::IOToken
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
      envVarT("EXTENSIBELLA_LIBRARY", ioin);
  --filenames for the standard library
  local baseFiles::[String] =
      ["bools", "integer_addition", "integer_multiplication",
       "integer_division", "integer_comparison", "lists", "strings",
       "pairs"];
  local fullFilenames::[String] =
      map(\ filename::String -> library_loc.iovalue ++ filename,
          baseFiles);
  return
     ioval(library_loc.io,
           if library_loc.iovalue == ""
           then left("Interface library location not set; " ++
                     "must run through given script")
           else right(fullFilenames));
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
