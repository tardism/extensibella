grammar extensibella:main;

imports extensibella:fromAbella;
imports extensibella:toAbella;
imports extensibella:common;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

imports silver:util:subprocess;
imports silver:util:cmdargs;


function mainProcess
IOVal<Integer> ::= 
   module_decl_parse::Parser<ModuleDecl_c>
   cmd_parse::Parser<AnyCommand_c>
   from_parse::Parser<FullDisplay_c>
   file_parse::Parser<FullFile_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c>
   largs::[String] ioin::IOToken
{
  local parsedArgs::Either<String Decorated CmdArgs> =
        parseArgs(largs);
  local generate::IOVal<Boolean> =
        generateSkeletonFiles(parsedArgs.fromRight.generateFiles,
           import_parse, interface_parse, outerface_parse, ioin);
  return
     case parsedArgs of
     | left(errs) -> ioval(printT(errs, ioin), 1)
     | right(args) ->
       if !generate.iovalue
       then ioval(generate.io, 1)
       else if (args.compileFile && args.checkFile)
       then check_compile_files(file_parse, from_parse, import_parse,
               interface_parse, outerface_parse, generate.io,
               args.filenames, args)
       else if args.compileFile
       then compile_files(file_parse, from_parse, import_parse,
               interface_parse, outerface_parse, generate.io,
               args.filenames, args)
       else if args.checkFile
       then run_files(file_parse, from_parse, import_parse,
               interface_parse, outerface_parse, generate.io,
               args.filenames, args)
       else if null(args.generateFiles)
       then run_interactive(module_decl_parse, import_parse,
               cmd_parse, from_parse, interface_parse,
               outerface_parse, ioin, args)
       else --don't run interactive if generating for some module(s)
            ioval(generate.io, 0)
     end;
}



type Parser<a> = (ParseResult<a> ::= String String);



synthesized attribute checkFile::Boolean occurs on CmdArgs;
synthesized attribute compileFile::Boolean occurs on CmdArgs;
synthesized attribute filenames::[String] occurs on CmdArgs;
--module and filename to generate skeletons for and into
synthesized attribute generateFiles::[(QName, String)] occurs on CmdArgs;

--whether we are running a file or interactive
synthesized attribute runningFile::Boolean occurs on CmdArgs;
--whether the user should see output
synthesized attribute showUser::Boolean occurs on CmdArgs;

--whether the Abella commands should be placed in the given file
--   Useful for debugging when the translation is wrong
synthesized attribute dumpAbella::Boolean occurs on CmdArgs;
synthesized attribute dumpAbellaFile::String occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.checkFile = false;
  top.compileFile = false;
  top.filenames = l;
  top.generateFiles = [];

  top.runningFile = !null(l);
  top.showUser = null(l);

  top.dumpAbella = false;
  top.dumpAbellaFile =
      error("Shouldn't access dumpAbellaFile if dumpAbella = false");
}


--Check the file for correctness
abstract production checkFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = true;
  top.compileFile = rest.compileFile;
  top.filenames = rest.filenames;
  top.generateFiles = rest.generateFiles;

  top.runningFile = true;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  forwards to rest;
}


--Compile the file to allow its theorems to be discovered for grammars
--   importing it
abstract production compileFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = rest.checkFile;
  top.compileFile = true;
  top.filenames = rest.filenames;
  top.generateFiles = rest.generateFiles;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  forwards to rest;
}


--Generate a file with the required imported theorems for proving
abstract production generateFlag
top::CmdArgs ::= moduleInfo::[String] rest::CmdArgs
{
  top.checkFile = rest.checkFile;
  top.compileFile = rest.compileFile;
  top.filenames = rest.filenames;
  top.generateFiles =
      case moduleInfo of
      | [mod, filename] ->
        (toQName(mod), filename)::rest.generateFiles
      | _ -> --should be checked by silver:util:cmdargs
        rest.generateFiles
      end;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = rest.dumpAbella;
  top.dumpAbellaFile = rest.dumpAbellaFile;

  forwards to rest;
}


--Dump translated commands to a file
abstract production dumpAbellaFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = rest.checkFile;
  top.compileFile = rest.compileFile;
  top.filenames = rest.filenames;
  top.generateFiles = rest.generateFiles;

  top.runningFile = rest.runningFile;
  top.showUser = rest.showUser;

  top.dumpAbella = true;
  top.dumpAbellaFile = "abella_dump.thm";

  forwards to rest;
}



function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  production attribute flags::[FlagSpec] with ++;
  flags := [];
  flags <-
     [flagSpec(name="--check",
               paramString=nothing(),
               help="check file for correctness and completion",
               flagParser=flag(checkFlag)),
      flagSpec(name="--compile",
               paramString=nothing(),
               help="compile file for importing into other modules",
               flagParser=flag(compileFlag)),
      flagSpec(name="--generate",
               paramString=just("<grammar> <filename>"),
               help="generate a basic theorem file for the given modules",
               flagParser=nOptions(2, generateFlag))];

  production attribute debugFlags::[FlagSpec] with ++;
  debugFlags := [];
  debugFlags <-
     [flagSpec(name="--dump-Abella",
               paramString=nothing(),
               help="dump translated Abella commands to a file",
               flagParser=flag(dumpAbellaFlag))];

  local usage::String = 
        "Usage: extensibella [options] [filenames]\n\n" ++
        "Flag options:\n" ++ flagSpecsToHelpText(flags) ++ "\n" ++
        "Debug flag options:\n" ++ flagSpecsToHelpText(debugFlags) ++
        "\n";

  -- Parse the command line
  production a::CmdArgs = interpretCmdArgs(flags ++ debugFlags, args);

  production attribute errors::[String] with ++;
  errors := if a.cmdError.isJust then [a.cmdError.fromJust] else [];

  errors <-
     if (a.checkFile || a.compileFile) && null(a.filenames)
     then ["Must give filename(s) with --check and --compile flags"]
     else [];

  errors <-
     if !null(a.filenames) && !(a.checkFile || a.compileFile)
     then ["Must specify at least one of --check or --compile " ++
           "when giving filename(s)"]
     else [];

  errors <-
     if !null(a.generateFiles) && !null(a.filenames)
     then ["Can give generate XOR filenames, not both"]
     else [];

  return if !null(errors)
         then left(implode("\n", errors) ++ "\n\n" ++ usage)
         else right(a);
}

