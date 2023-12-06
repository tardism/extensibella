grammar extensibella:main:compose;

function compose_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  local gathered::IOVal<Either<String [(QName, Decorated ListOfCommands)]>> =
      gatherProofFiles(parsers, config, config.filenames, ioin);

  return case gathered.iovalue of
         | left(err) -> ioval(printT(err, gathered.io), 1)
         | right(_) -> ioval(ioin, 1)
         end;
}


--gather the executed proof files by module name
function gatherProofFiles
IOVal<Either<String [(QName, Decorated ListOfCommands)]>> ::=
   parsers::AllParsers config::Configuration filenames::[String]
   ioin::IOToken
{
  local filename::String = head(filenames);

  --initial set-up for file
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement]))>> =
      processFile(filename, parsers, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement]) =
      fileInfo.iovalue.fromRight.snd;

  --run it
  local runFile::Either<IOVal<String>  Decorated ListOfCommands> =
      buildDecRunCommands(filename, fileAST.2, parsers, fileAST.1.fromJust,
         processed.1, processed.2, processed.3, config, fileInfo.io);
  local runIO::IOToken = --pull out an IOToken
      case runFile of
      | left(errIO) -> errIO.io
      | right(cmds) -> cmds.runResult.io
      end;

  --do it all again
  local rest::IOVal<Either<String [(QName, Decorated ListOfCommands)]>> =
      gatherProofFiles(parsers, config, tail(filenames), runIO);


  return case filenames of
         | [] -> ioval(ioin, right([]))
         | _::_ ->
           if !fileInfo.iovalue.isRight
           then ioval(fileInfo.io,
                      left("Error for file " ++ filename ++ ":  "  ++
                           fileInfo.iovalue.fromLeft ++ "\n"))
           else case runFile of
                | left(errIO) ->
                  ioval(errIO.io,
                        left("Error for file " ++ filename ++ ":  " ++
                             errIO.iovalue ++ "\n"))
                | right(cmds) ->
                  ioval(rest.io,
                        case rest.iovalue of
                        | left(x) -> left(x)
                        | right(l) ->
                          right((fileAST.1.fromJust, cmds)::l)
                        end)
                end
         end;
}
