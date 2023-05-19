grammar extensibella:main;

{-
  Output nicely-formatted HTML of the interaction, including both
  commands and outputs, with each command having its own HTML element
  ID number (in order from the start)
-}

aspect function run
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
  cmds.htmlID = 1;
}

inherited attribute htmlID::Integer;

attribute
   htmlID
occurs on ListOfCommands;


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  --Annotated HTML file with command and non-dying output
  io <- \ i::IOToken ->
          if top.config.outputAnnotated
          then appendFileT(top.config.annotatedFile,
                  --create block
                  "<pre class=\"code extensibella\"" ++
                       "id=\"" ++ toString(top.htmlID) ++ "\">\n" ++
                    --add prompt and command
                    " &lt; <b>" ++ stripExternalWhiteSpace(
                                      makeHTMLSafe(
                                         showDoc(80,
                                            nest(3, any_a.pp)))) ++
                          "</b>\n\n" ++
                    --Extensibella output
                    stripExternalWhiteSpace(
                       makeHTMLSafe(output_output)) ++ "\n" ++
                  --end block
                  "</pre>\n",
                  i)
          else i;

  rest.htmlID = top.htmlID + 1;
}




{-
  In the HTML output, the extension size and translation versions of a
  relation are disappearing because they are treated as tags.  This
  replaces the literal "<" and ">" with HTML-safe versions.
-}
function makeHTMLSafe
String ::= s::String
{
  return substitute("<", "&lt;", substitute(">", "&gt;", s));
}





--whether the Extensibella commands and output should be placed in the
--given file
synthesized attribute outputAnnotated::Boolean occurs on CmdArgs;
synthesized attribute annotatedFile::String occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.outputAnnotated = false;
  top.annotatedFile =
      error("Shouldn't access annotatedFile if outputAnnotated = false");
}


--Output an HTML version of the commands with the Extensibella output
abstract production annotatedOutputFlag
top::CmdArgs ::= name::String rest::CmdArgs
{
  --if there are files, this requires checking
  top.checkFile = rest.checkFile || !null(rest.filenames);
  top.compileFile = rest.compileFile;
  top.filenames = rest.filenames;
  top.generateFiles = rest.generateFiles;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  top.displayHelp = rest.displayHelp;

  top.outputAnnotated = true;
  top.annotatedFile = name;

  forwards to rest;
}


aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--annotate",
               paramString=just("<filename>"),
               help="output an HTML version of the interaction",
               flagParser=option(annotatedOutputFlag))];

  errors <-
     if a.outputAnnotated && length(a.filenames) > 1
     then ["Can only check one file with annotated HTML output; " ++
           "multiple files would all be in the same HTML file"]
     else [];
}
