grammar extensibella:main;

imports extensibella:main:util;
imports extensibella:main:run;
imports extensibella:main:compile;
imports extensibella:main:generate;

imports silver:util:cmdargs;


function mainProcess
IOVal<Integer> ::= parsers::AllParsers largs::[String] ioin::IOToken
{
  local parsedArgs::Either<String Decorated CmdArgs> =
        parseArgs(largs);

  {-
    Actions to run, choosing whether or not to run them based on the
    command line arguments received
    If one fails (returns .iovalue != 0), the ones after will not run
  -}
  production attribute actions::[ActionSpec] with ++;
  actions :=
      [actionSpec(
          runFun = check_compile_files,
          shouldDoFun = \ c::Configuration ->
                          c.checkFile && c.compileFile,
          actionDesc = "Check and Compile"),
       actionSpec(
          runFun = run_files,
          shouldDoFun = \ c::Configuration ->
                          c.checkFile && !c.compileFile,
          actionDesc = "Check"),
       actionSpec(
          runFun = compile_files,
          shouldDoFun = \ c::Configuration ->
                          !c.checkFile && c.compileFile,
          actionDesc = "Compile"),
       actionSpec(
          runFun = generateSkeletonFiles,
          shouldDoFun = \ c::Configuration ->
                          !null(c.generateFiles),
          actionDesc = "Generate")
      ];

  {-
    Whether to run the REPL for Extensibella
    Should be true if no other action is given
  -}
  production attribute runREPL::Boolean with &&;
  runREPL :=
      case parsedArgs of
      | left(_) -> false --parse failure is just print errors
      | right(a) ->
        !a.checkFile && !a.compileFile && null(a.generateFiles)
      end;

  return
      case parsedArgs of
      | left(errs) -> ioval(printT(errs, ioin), 1)
      | right(a) ->
        let i::IOVal<Integer> = runActions(actions, parsers, a, ioin)
        in
          if i.iovalue != 0 || !runREPL
          then i
          else run_interactive(parsers, i.io, a)
        end
      end;
}






--run all the actions in the order in which they occur
function runActions
IOVal<Integer> ::= actions::[ActionSpec] parsers::AllParsers
                   config::Configuration ioin::IOToken
{
  local act::ActionSpec = head(actions);
  local runAct::IOVal<Integer> =
      act.runFun(parsers, ioin, config);

  return
      case actions of
      | [] -> ioval(ioin, 0)
      | _::tl when act.shouldDoFun(config) ->
        if runAct.iovalue != 0 --error in this action
        then runAct
        else runActions(tl, parsers, config, runAct.io)
      | _::tl -> runActions(tl, parsers, config, ioin)
      end;
}


nonterminal ActionSpec with runFun, shouldDoFun, actionDesc;
--How to run the action (return 0 for success, non-zero for fail)
--   result ::= compiled mods  gen loc  grammars loc  args  io
annotation runFun::(IOVal<Integer> ::= AllParsers IOToken
                                       Configuration);
--Whether to run the action (true => run, false => skip)
--Should not do any IO actions
annotation shouldDoFun::(Boolean ::= Configuration);
--A short name/description of the action, currently for debugging
--May be made part of the standard output in the future
annotation actionDesc::String;

production actionSpec
top::ActionSpec ::=
{ }






--Run through a list of files, checking and compiling them
function check_compile_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Decorated CmdArgs
{
  return foldl(\ thusFar::IOVal<Integer> f::String ->
                 if thusFar.iovalue == 0
                 then let r::IOVal<Integer> =
                          run_file(parsers, thusFar.io, f, config)
                      in
                        if r.iovalue == 0
                        then compile_file(parsers, r.io, f, config)
                        else r
                      end
                 else thusFar,
               ioval(ioin, 0), config.filenames);
}
