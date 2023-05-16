grammar extensibella:main;


--Run a REPL for the theorem prover
--First entry must be a module declaration (Module na:me.)
function run_interactive
IOVal<Integer> ::=
   module_decl_parse::Parser<ModuleDecl_c>
   import_parse::Parser<ListOfCommands_c>
   cmd_parse::Parser<AnyCommand_c>
   from_parse::Parser<FullDisplay_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c>
   ioin::IOToken config::Decorated CmdArgs
{
  --get the module information
  local processed::IOVal<Maybe<(QName, ListOfCommands, [DefElement],
                                [ThmElement])>> =
      get_module_interactive(module_decl_parse, import_parse,
         interface_parse, outerface_parse, ioin);

  return
     if !processed.iovalue.isJust
     then ioval(processed.io, 0) --quit, so return
     else run("<<user input>>", build_interactive_commands(cmd_parse),
              import_parse, from_parse, processed.iovalue.fromJust.1,
              processed.iovalue.fromJust.2,
              processed.iovalue.fromJust.3,
              processed.iovalue.fromJust.4, config, processed.io);
}


--Continue trying to get a module declaration from the user until
--   they actually give one
function get_module_interactive
IOVal<Maybe<(QName, ListOfCommands, [DefElement], [ThmElement])>> ::=
   module_decl_parse::Parser<ModuleDecl_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
{
  --Get input
  local printed_prompt::IOToken = printT(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);

  --Process input
  local result::ParseResult<ModuleDecl_c> =
      module_decl_parse(input, "<<input>>");
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
      processModuleDecl(result.parseTree.ast.fromJust, import_parse,
         interface_parse, outerface_parse, raw_input.io);

  return
     if !result.parseSuccess
     then get_module_interactive(module_decl_parse, import_parse,
             interface_parse, outerface_parse,
             printT("Error:  First entry must be a module\n" ++
                    result.parseErrors ++ "\n\n", raw_input.io))
     else if !result.parseTree.ast.isJust
     then ioval(raw_input.io, nothing()) --quit
     else case processed.iovalue of
          | left(err) ->
            get_module_interactive(module_decl_parse, import_parse,
               interface_parse, outerface_parse,
               printT("Error:  " ++ err ++ "\n\n", processed.io))
          | right((a, b, c)) ->
            ioval(processed.io,
                  just((result.parseTree.ast.fromJust, a, b, c)))
          end;
}


--Create a list of commands by reading them from the user
function build_interactive_commands
[AnyCommand] ::=
   cmd_parse::(ParseResult<AnyCommand_c> ::= String String)
{
  local printed_prompt::IOToken = printT(" < ", unsafeIO());
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);
  local result::ParseResult<AnyCommand_c> =
        cmd_parse(input, "<<input>>");
  local any_a::AnyCommand =
        if result.parseSuccess
        then result.parseTree.ast
        else anyParseFailure(result.parseErrors);
  return if isSpace(input)
         then build_interactive_commands(cmd_parse)
         else any_a::build_interactive_commands(cmd_parse);
}






{--------------------------------------------------------------------
                           READ USER INPUT                           
 --------------------------------------------------------------------}
{-
  Read the command, which may be several lines, from stdin.
-}
function read_full_input
IOVal<String> ::= ioin::IOToken
{
  return read_full_input_comments(ioin, 0);
}
{-
  Read the command, keeping track of open multi-line comments to
  ensure reading in a full command, rather than just part of one and
  part of an open comment
-}
function read_full_input_comments
IOVal<String> ::= ioin::IOToken openComments::Integer
{
  local read::IOVal<Maybe<String>> = readLineStdinT(ioin);
  local newOpenComments::Integer =
        count_comments(read.iovalue.fromJust, openComments);
  local readRest::IOVal<String> =
        read_full_input_comments(read.io, newOpenComments);
  local noWhiteSpace::String =
        stripExternalWhiteSpace(read.iovalue.fromJust);
  local shouldEnd::Boolean = endsWith(".", noWhiteSpace);
  return
     if !read.iovalue.isJust
     then ioval(read.io, "Quit.") --^D entered, I think
     else if openComments < 0
     then ioval(read.io, read.iovalue.fromJust) --syntax error
     else if openComments > 0
     then ioval(readRest.io,
                read.iovalue.fromJust ++ "\n" ++ readRest.iovalue)
     else if shouldEnd
     then ioval(read.io, read.iovalue.fromJust)
     else ioval(readRest.io,
                read.iovalue.fromJust ++ "\n" ++ readRest.iovalue);
}
--Return number of open comments after line
function count_comments
Integer ::= line::String openComments::Integer
{
  local stringStart::Integer = indexOf("\"", line);
  local lineStart::Integer = indexOf("%", line);
  local multiStart::Integer = indexOf("/*", line);
  local multiEnd::Integer = indexOf("*/", line);
  return
     if openComments < 0
     then openComments --syntax error
     else if openComments > 0
     then if multiEnd >= 0
          then count_comments(substring(multiEnd + 2, length(line),
                                        line), openComments - 1)
          else openComments
     --openComments == 0
     else if lineStart >= 0 &&
             (stringStart < 0 || lineStart < stringStart) &&
             (multiStart < 0 || lineStart < multiStart)
     then 0 --is line comment, so nothing else matters
     else if stringStart >= 0 &&
             (multiStart < 0 || stringStart < lineStart)
     then count_comments(clear_string(substring(stringStart + 1,
                                                length(line), line)),
                         openComments)
     else if multiStart >= 0
     then count_comments(substring(multiStart + 2, length(line), line),
                         openComments + 1)
     else 0; --nothing special in this line
}
--Remove a quoted string from the beginning of a line
function clear_string
String ::= line::String
{
  local quote::Integer = indexOf("\"", line);
  local slashquote::Integer = indexOf ("\\\"", line); --\"
  return
     if quote < slashquote --quote must be found for valid syntax
     then substring(quote + 1, length(line), line)
     else clear_string(substring(slashquote + 2, length(line), line));
}

