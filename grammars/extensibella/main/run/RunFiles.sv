grammar extensibella:main:run;


--Run through a list of files, checking them for validity
function run_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  return foldl(\ thusFar::IOVal<Integer> f::String ->
                 if thusFar.iovalue == 0
                 then run_file(parsers, thusFar.io, f, config)
                 else thusFar,
               ioval(ioin, 0), config.filenames);
}


--Run through a file to check that all the proofs are done correctly
function run_file
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken filename::String
                   config::Decorated CmdArgs
{
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement]))>> =
      processFile(filename, parsers, ioin);
  production fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  production processed::(ListOfCommands, [DefElement], [ThmElement]) =
      fileInfo.iovalue.fromRight.snd;

  --Permit the addition of extra actions to be carried out after the
  --processing above
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;

  local finalIOToken::IOToken = io(fileInfo.io);

  return
     case fileInfo.iovalue of
     | left(err) -> ioval(printT(err, finalIOToken), 1)
     | right(_) ->
       run(filename, fileAST.2, parsers, fileAST.1.fromJust,
           processed.1, processed.2, processed.3, config,
           finalIOToken)
     end;
}
