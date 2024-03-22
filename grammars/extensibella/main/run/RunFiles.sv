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
                   config::Configuration
{
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement],
                      [(QName, [QName])]))>> =
      processFile(filename, parsers, ioin);
  production fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  production processed::(ListOfCommands, [DefElement], [ThmElement],
                         [(QName, [QName])]) =
      fileInfo.iovalue.fromRight.snd;

  --Permit the addition of extra actions to be carried out after the
  --processing above
  production attribute io::(IOToken ::= IOToken) with combineIO;
  io := \ i::IOToken -> i;
  io <- dumpOrder(processed.3, config, _);

  local finalIOToken::IOToken = io(fileInfo.io);

  return
     case fileInfo.iovalue of
     | left(err) -> ioval(printT(err, finalIOToken), 1)
     | right(_) ->
       run(filename, fileAST.2.toRunCommands, parsers,
           fileAST.1.fromJust, processed.1, processed.2, processed.3,
           processed.4, config, finalIOToken)
     end;
}


--Print out the order of imported elements
function dumpOrder
IOToken ::= order::[ThmElement] config::Configuration ioin::IOToken
{
  local orderString::String =
      "\n\n\nObligation Order:\n" ++
      implode("\n",
         map(\ t::ThmElement ->
               case t of
               | nonextensibleTheorem(n, _, _) ->
                 "Theorem " ++ justShow(n.pp)
               | splitElement(n, ns) ->
                 "Split " ++ justShow(n.pp) ++ " as " ++
                 implode(", ", map(justShow, map((.pp), ns))) ++ "."
               | extensibleMutualTheoremGroup(thms, alsos, tag) ->
                 "ExtTheorem " ++
                 implode(", ", map(justShow,
                                   map((.pp), map(fst, thms)))) ++ "."
               | projectionConstraintTheorem(n, _, _, tag) ->
                 "PC " ++ justShow(n.pp) ++ "."
               | extIndElement(r, tag) ->
                 "ExtInd " ++
                 implode(", ", map(justShow,
                                   map((.pp), map(fst, r)))) ++ "."
               | extSizeElement(r, tag) ->
                 "ExtSize " ++
                 implode(", ", map(justShow,
                                   map((.pp), map(fst, r)))) ++ "."
               end,
             order)) ++ "\n\n\n";

  return if config.dumpOrder
         then printT(orderString, ioin)
         else ioin;
}
