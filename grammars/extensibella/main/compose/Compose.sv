grammar extensibella:main:compose;

function compose_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  local composeModule::QName = toQName(config.composeModuleName);

  local genDirs::IOVal<[String]> = getGenDirs(ioin);

  --interface file to know the modules we should have
  local interfaceFileLoc::IOVal<Maybe<String>> =
      findFile(composeModule.interfaceFileName, genDirs.iovalue, genDirs.io);
  local interfaceFileContents::IOVal<String> =
      readFileT(interfaceFileLoc.iovalue.fromJust, interfaceFileLoc.io);
  local parsedMods::ParseResult<ModuleList_c> =
      parsers.interface_parse(interfaceFileContents.iovalue,
                              interfaceFileLoc.iovalue.fromJust);
  local interface::ImportedModuleList = parsedMods.parseTree.ast;
  local expectedMods::[QName] = --reverse to put host first
      reverse(interface.mods) ++
      --add because interface file doesn't include the module itself
      [^composeModule];
  local buildsOns::[(QName, [QName])] =
      (^composeModule, interface.mods)::interface.buildsOns;

  --definition file
  local composedDefFileLoc::IOVal<Maybe<String>> =
      findFile(composeModule.composedFileName, genDirs.iovalue,
               interfaceFileContents.io);
  local defFileContents::IOVal<String> =
      readFileT(composedDefFileLoc.iovalue.fromJust, composedDefFileLoc.io);
  local parsedDefFile::ParseResult<ListOfCommands_c> =
      parsers.import_parse(defFileContents.iovalue,
                           composedDefFileLoc.iovalue.fromJust);
  local defEnvs::(Env<TypeEnvItem>, Env<RelationEnvItem>,
                  Env<ConstructorEnvItem>) =
      module_elements(parsedDefFile.parseTree.ast);
  local standInRules::[(QName, Def)] =
      parsedDefFile.parseTree.ast.standInRules;

  --gather modules and check the right ones are there
  local gathered::IOVal<Either<String [(QName, String, DecCmds)]>> =
      gatherProofFiles(parsers, config, config.filenames, defFileContents.io);
  local checkMods::Either<String [(QName, DecCmds)]> =
      checkModulesMatch(expectedMods, gathered.iovalue.fromRight);

  --get the proof definitions and obligations
  local outerface::IOVal<Either<String ([DefElement], [ThmElement])>> =
      readOuterfaces(parsedMods.parseTree.ast.mods, --don't need outerface for composeMod
                     parsers, genDirs.iovalue, gathered.io);

  --gather thm information for building proofs
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(parsers, outerface.io);
  local allThms::[(QName, Metaterm)] = stdLibThms.iovalue.fromRight;

  --build and write the file, now that everything has checked out
  local createComposedFile::IOVal<Integer> =
      build_composed_file(config.composeFilename, defFileContents.iovalue,
         checkMods.fromRight, outerface.iovalue.fromRight.1,
         defEnvs.2, defEnvs.3, defEnvs.1, standInRules,
         outerface.iovalue.fromRight.2, config, parsers, allThms,
         buildsOns, stdLibThms.io);

  return
      --interface errors
      if !interfaceFileLoc.iovalue.isJust
      then ioval(printT("Could not find interface file for module " ++
                        justShow(composeModule.pp) ++
                        "; must compile module first",
                        interfaceFileLoc.io), 1)
      else if !parsedMods.parseSuccess
      then ioval(printT("Could not parse interface file for module " ++
                        justShow(composeModule.pp) ++ ":\n" ++
                        parsedMods.parseErrors ++ "\n",
                        interfaceFileContents.io), 1)
      --definition errors
      else if !composedDefFileLoc.iovalue.isJust
      then ioval(printT("Could not find composed definition file for module " ++
                        justShow(composeModule.pp) ++
                        "; must compile module for composition first",
                        composedDefFileLoc.io), 1)
      else if !parsedDefFile.parseSuccess
      then ioval(printT("Could not parse definition file for module " ++
                        justShow(composeModule.pp) ++ ":\n" ++
                        parsedDefFile.parseErrors ++ "\n",
                        defFileContents.io), 1)
      --module gathering and checking errors
      else if !gathered.iovalue.isRight
      then ioval(printT(gathered.iovalue.fromLeft, gathered.io), 1)
      else if !checkMods.isRight
      then ioval(printT(checkMods.fromLeft, gathered.io), 1)
      else if !outerface.iovalue.isRight
      then ioval(printT(outerface.iovalue.fromLeft, outerface.io), 1)
      else createComposedFile;
}


--gather the executed proof files by module name
function gatherProofFiles
IOVal<Either<String [(QName, String, DecCmds)]>> ::=
   parsers::AllParsers config::Configuration filenames::[String]
   ioin::IOToken
{
  local filename::String = head(filenames);

  --initial set-up for file
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement],
                      [(QName, [QName])]))>> =
      processFile(filename, parsers, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement],
                    [(QName, [QName])]) =
      fileInfo.iovalue.fromRight.snd;

  --run it
  local runFile::Either<IOVal<String>  DecCmds> =
      buildDecRunCommands(filename, fileAST.2.toRunCommands, parsers,
         fileAST.1.fromJust, processed.1, processed.2, processed.3,
         processed.4, config, fileInfo.io);
  local runIO::IOToken = --pull out an IOToken
      case runFile of
      | left(errIO) -> errIO.io
      | right(cmds) -> cmds.runResult.io
      end;

  --do it all again
  local rest::IOVal<Either<String [(QName, String, DecCmds)]>> =
      gatherProofFiles(parsers, config, tail(filenames), runIO);

  return case filenames of
         | [] -> ioval(ioin, right([]))
         | _::_ ->
           if !fileInfo.iovalue.isRight
           then ioval(fileInfo.io,
                      left("Error processing file " ++ filename ++
                           ":  "  ++ fileInfo.iovalue.fromLeft ++ "\n"))
           else case runFile of
                | left(errIO) ->
                  ioval(errIO.io,
                        left("Error processing file " ++ filename ++
                             ":  " ++ errIO.iovalue ++ "\n"))
                | right(cmds) ->
                  if cmds.runResult.iovalue != 0
                  then ioval(cmds.runResult.io,
                             left("File " ++ filename ++ " is not valid\n"))
                  else ioval(rest.io,
                             case rest.iovalue of
                             | left(x) -> left(x)
                             | right(l) ->
                               right((fileAST.1.fromJust, filename, cmds)::l)
                             end)
                end
         end;
}


{-
  Check the expected modules and found modules match; it is an error
  if there is not a one-to-one mapping between them
  @param expectedMods  modules that should be present
  @param foundMods  parsed and run files given by user
  @return  error message, if there is an error, or re-ordered file list
-}
function checkModulesMatch
Either<String [(QName, DecCmds)]> ::= expectedMods::[QName]
                                      foundMods::[(QName, String, DecCmds)]
{
  local allFiles::[(String, DecCmds)] =
      lookupAll(head(expectedMods), foundMods);
  local removeFiles::[(QName, String, DecCmds)] =
      filter(\ p::(QName, String, DecCmds) -> p.1 != head(expectedMods),
             foundMods);

  return
      case expectedMods, foundMods of
      --successfully finished
      | [], [] -> right([])
      --out of modules, extra files
      | [], [(q, f, c)] -> left("Extra proof file " ++ f ++ "\n")
      | [], l ->
        left("Extra proof files " ++
             implode(", ", map(\ p::(QName, String, DecCmds) -> p.2, l)) ++ "\n")
      --no more files for modules
      | [m], [] -> left("Missing proof file for module " ++ justShow(m.pp) ++ "\n")
      | l, [] ->
        left("Missing proof files for modules " ++
             implode(", ", map(\ m::QName -> justShow(m.pp), l)) ++ "\n")
      --step
      | m::tl, _::_ ->
        case allFiles of
        | [] -> left("Missing proof file for module " ++ justShow(m.pp) ++ "\n")
        | [(f, c)] -> bind(checkModulesMatch(tl, removeFiles),
                           \ l::[(QName, DecCmds)] -> right((m, c)::l))
        | l ->
          left("Multiple proof files for module " ++ justShow(m.pp) ++ ":  " ++
               implode(", ", map(\ p::(String, DecCmds) -> p.1, l)) ++ "\n")
        end
      end;
}


--make the string for the composed file and write it out to the file
function build_composed_file
IOVal<Integer> ::= outFilename::String defFileContents::String
                   mods::[(QName, DecCmds)] proofDefs::[DefElement]
                   defRelEnv::Env<RelationEnvItem>
                   defConstrEnv::Env<ConstructorEnvItem>
                   defTyEnv::Env<TypeEnvItem> standInRules::[(QName, Def)]
                   thms::[ThmElement]
                   config::Configuration parsers::AllParsers
                   allThms::[(QName, Metaterm)] buildsOns::[(QName, [QName])]
                   ioin::IOToken
{
  --Extensibella standard library
  local stdLib::IOVal<[String]> = extensibellaStdLibAbellaCmds(ioin);
  local stdLibString::String =
      "/********************************************************************\n" ++
      " Extensibella Standard Library\n" ++
      " ********************************************************************/\n" ++
      implode("\n", stdLib.iovalue) ++ "\n\n\n";

  --language definition
  local langDefString::String =
      "/********************************************************************\n" ++
      " Language Definition\n" ++
      " ********************************************************************/\n" ++
      defFileContents ++ "\n\n\n";

  --things we'll need for proof processing
  local proofDefItems::([TypeEnvItem], [RelationEnvItem],
                        [ConstructorEnvItem], [[QName]]) =
      defElementsDefinitions(proofDefs);
  local proverState::ProverState =
      defaultProverState([],
         addEnv(defTyEnv, proofDefItems.1),
         addEnv(defRelEnv, proofDefItems.2),
         addEnv(defConstrEnv, proofDefItems.3),
         proofDefItems.4, [], buildsOns);

  --proof definitions
  local encodedProofDefs::[AnyCommand] =
      flatMap(\ c::AnyCommand ->
                decorate c with {
                   priorStep = error("priorStep not needed");
                   proverState = proverState;
                   typeEnv = proverState.knownTypes;
                   relationEnv = proverState.knownRels;
                   constructorEnv = proverState.knownConstrs;
                   currentModule = error("currentModule not needed");
                   boundNames = [];
                }.toAbella,
              flatMap((.encode), proofDefs));
  local fullProofDefs::[String] =
      map((.abella_pp), encodedProofDefs) ++
      flatMap(buildExtIndDefs(_, proverState, standInRules, buildsOns), thms);
  local proofDefsString::String =
      if null(fullProofDefs) then ""
      else "/********************************************************************\n" ++
           " Proof-Level Definitions\n" ++
           " ********************************************************************/\n" ++
           implode("\n", fullProofDefs) ++ "\n\n\n";

  --properties and proofs
  local abella::IOVal<Either<String ProcessHandle>> =
      startAbella(stdLib.io, config);
  local sendAbellaDefs::IOVal<String> =
      sendBlockToAbella(langDefString ++ proofDefsString,
         abella.iovalue.fromRight, abella.io, config);
  local propertyString::String =
      "/********************************************************************\n" ++
      " Properties and Proofs\n" ++
      " ********************************************************************/\n";

  --put it all together to output before building proofs
  local fullString::String =
      stdLibString ++ langDefString ++ proofDefsString ++ propertyString;
  local output::IOToken =
      writeFileT(outFilename, fullString,
         printT("Writing " ++ outFilename ++ "...",
                sendAbellaDefs.io));

  --compose the proofs and write them to the file
  local builtProps::IOToken =
      compose_proofs(thms, mods, proverState, abella.iovalue.fromRight,
         parsers, config, outFilename, allThms, [], [], buildsOns, output);

  --clean up by quitting Abella
  local quitAbella::IOToken =
      exitAbella([anyNoOpCommand(quitCommand())], builtProps,
         abella.iovalue.fromRight, false, config);

  return ioval(printT("Done\n", builtProps), 0);
}


--defs for R_{ES} and R_P for everything needing them
function buildExtIndDefs
[String] ::= thm::ThmElement proverState::ProverState
             standInRules::[(QName, Def)] buildsOns::[(QName, [QName])]
{
  thm.relEnv = proverState.knownRels;
  thm.constrEnv = proverState.knownConstrs;
  thm.tyEnv = proverState.knownTypes;
  thm.standInRules_down = standInRules;
  thm.buildsOns_down = buildsOns;
  return thm.extIndDefs;
}


--pull the modular proofs apart and build the full text proof
function compose_proofs
IOToken ::= thms::[ThmElement] mods::[(QName, DecCmds)]
   proverState::ProverState abella::ProcessHandle
   parsers::AllParsers config::Configuration outfilename::String
   allThms::[(QName, Metaterm)] knownExtSizes::[[QName]]
   knownExtInds::[(QName, [String], Bindings, ExtIndPremiseList)]
   buildsOns::[(QName, [QName])] ioin::IOToken
{
  local sub::([(QName, DecCmds)], [(QName, Metaterm)], [[QName]],
              [(QName, [String], Bindings, ExtIndPremiseList)], IOToken) =
      handleFstThm(outfilename, mods, head(thms), proverState, abella,
         parsers, config, allThms, knownExtSizes, knownExtInds, buildsOns,
         ioin);
  local again::IOToken =
      compose_proofs(tail(thms), sub.1, proverState, abella, parsers,
                     config, outfilename, sub.2 ++ allThms,
                     sub.3 ++ knownExtSizes, sub.4 ++ knownExtInds,
                     buildsOns, sub.5);

  return
      case thms of
      | [] -> ioin
      | _::rest -> again
      end;
}

--Decorate this here rather than in compose_proofs directly for memory
--   efficiency so it can throw the decorated tree away
--Printing here saves on memory, as opposed to building up the string
--   and passing it up to build_composed_file, since we force the
--   string thunk earlier
function handleFstThm
([(QName, DecCmds)], [(QName, Metaterm)], [[QName]],
 [(QName, [String], Bindings, ExtIndPremiseList)], IOToken) ::=
   outfilename::String mods::[(QName, DecCmds)]
   fstThm::ThmElement proverState::ProverState abella::ProcessHandle
   parsers::AllParsers config::Configuration
   allThms::[(QName, Metaterm)] knownExtSizes::[[QName]]
   knownExtInds::[(QName, [String], Bindings, ExtIndPremiseList)]
   buildsOns::[(QName, [QName])] ioin::IOToken
{
  fstThm.incomingMods = mods;
  fstThm.relEnv = proverState.knownRels;
  fstThm.constrEnv = proverState.knownConstrs;
  fstThm.tyEnv = proverState.knownTypes;
  --
  fstThm.allThms = allThms;
  fstThm.knownExtSizes_down = knownExtSizes;
  fstThm.knownExtInds_down = knownExtInds;
  fstThm.buildsOns_down = buildsOns;
  --
  fstThm.liveAbella = abella;
  fstThm.runAbella = ioin;
  fstThm.configuration = config;
  fstThm.allParsers = parsers;

  local output::IOToken =
      appendFileT(outfilename, fstThm.composedCmds,
                  fstThm.runAbella_out);

     --drop the non-extensible things, like definitions, from all modules
  return (dropNonProof(fstThm.outgoingMods), fstThm.newThms,
          fstThm.newExtSizes, fstThm.newExtInds, output);
}
