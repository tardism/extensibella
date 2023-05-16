grammar extensibella:main;


--Run through a list of files, checking them for validity
function run_files
IOVal<Integer> ::=
   file_parse::Parser<FullFile_c> from_parse::Parser<FullDisplay_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
   filenames::[String] config::Decorated CmdArgs
{
  local ran::IOVal<Integer> =
      run_file(file_parse, from_parse, import_parse,
               interface_parse, outerface_parse, ioin,
               head(filenames), config);
  return
      case filenames of
      | [] -> ioval(ioin, 0)
      | hd::tl ->
        if ran.iovalue != 0
        then ran --error in that file, so quit
        else run_files(file_parse, from_parse, import_parse,
                interface_parse, outerface_parse, ran.io, tl, config)
      end;
}


--Run through a file to check that all the proofs are done correctly
function run_file
IOVal<Integer> ::=
   file_parse::Parser<FullFile_c> from_parse::Parser<FullDisplay_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c>
   ioin::IOToken filename::String config::Decorated CmdArgs
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local fileContents::IOVal<String> =
        readFileT(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
        file_parse(fileContents.iovalue, filename);
  local fileAST::(Maybe<QName>, ListOfCommands) =
        fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
      processModuleDecl(fileAST.1.fromJust, import_parse,
          interface_parse, outerface_parse, fileContents.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
      startAbella(processed.io, config);
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(import_parse, started.io);
  --basic context information from the definition file
  local build_context::IOVal<(Env<TypeEnvItem>, Env<RelationEnvItem>,
                              Env<ConstructorEnvItem>)> =
      set_up_abella_module(fileAST.1.fromJust,
         processed.iovalue.fromRight.1,
         processed.iovalue.fromRight.2, from_parse,
         started.iovalue.fromRight, stdLibThms.io, config);
  --context information for imported definitions
  local importedProofDefs::([TypeEnvItem], [RelationEnvItem],
                            [ConstructorEnvItem]) =
      defElementsDefinitions(processed.iovalue.fromRight.2);
  --combine definition file and imported proof definitions
  local startProverState::ProverState =
      defaultProverState(processed.iovalue.fromRight.3,
         addEnv(build_context.iovalue.1, importedProofDefs.1),
         addEnv(build_context.iovalue.2, importedProofDefs.2),
         addEnv(build_context.iovalue.3, importedProofDefs.3),
         stdLibThms.iovalue.fromRight);
  --
  local handleIncoming::([AnyCommand], ProverState) =
      handleIncomingThms(startProverState);
  local sendIncoming::IOVal<String> =
      sendCmdsToAbella(map((.abella_pp), handleIncoming.1),
         started.iovalue.fromRight, build_context.io, config);

  return
     if !fileExists.iovalue
     then ioval(printT("Given file " ++ filename ++ " does not exist\n",
                       fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(printT("Syntax error:\n" ++ fileParsed.parseErrors ++
                       "\n", fileContents.io), 1)
     else if !fileAST.1.isJust
     then ioval(printT("Error:  Module declaration cannot be Quit " ++
                       "in " ++ filename ++ "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(printT("Error:  " ++ processed.iovalue.fromLeft ++
                       "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else if !stdLibThms.iovalue.isRight
     then ioval(printT("Error:  " ++ stdLibThms.iovalue.fromLeft ++
                       "\n", stdLibThms.io), 1)
     else run_step(
             fileAST.2.commandList,
             filename,
             from_parse,
             fileAST.1.fromJust,
             [(-1, handleIncoming.2)],
             config,
             started.iovalue.fromRight,
             sendIncoming.io);
}
