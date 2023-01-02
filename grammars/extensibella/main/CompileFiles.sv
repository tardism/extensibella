grammar extensibella:main;


--Run through a list of files, compiling them
function compile_files
IOVal<Integer> ::=
   file_parse::Parser<FullFile_c> from_parse::Parser<FullDisplay_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
   filenames::[String] config::Decorated CmdArgs
{
  local compiled::IOVal<Integer> =
      compile_file(file_parse, from_parse, import_parse,
         interface_parse, outerface_parse, ioin, head(filenames));
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if compiled.iovalue != 0
       then compiled --error in compiling that file, so quit
       else compile_files(file_parse, from_parse, import_parse,
               interface_parse, outerface_parse, compiled.io, tl,
               config)
     end;
}


--Run through a list of files, checking and compiling them
function check_compile_files
IOVal<Integer> ::=
   file_parse::Parser<FullFile_c> from_parse::Parser<FullDisplay_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
   filenames::[String] config::Decorated CmdArgs
{
  local ran::IOVal<Integer> =
      run_file(file_parse, from_parse, import_parse,
          interface_parse, outerface_parse, ioin, head(filenames),
          config);
  local compiled::IOVal<Integer> =
      compile_file(file_parse, from_parse, import_parse,
          interface_parse, outerface_parse, ran.io, head(filenames));
  return
      case filenames of
      | [] -> ioval(ioin, 0)
      | hd::tl ->
        if ran.iovalue != 0
        then ran --error in checking that file, so quit
        else if compiled.iovalue != 0
        then compiled --error in compiling that file, so quit
        else check_compile_files(file_parse, from_parse, import_parse,
                interface_parse, outerface_parse, compiled.io, tl,
                config)
      end;
}


--Compile a file, outputting it into the generated directory
function compile_file
IOVal<Integer> ::=
   file_parse::Parser<FullFile_c> from_parse::Parser<FullDisplay_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c>
   ioin::IOToken filename::String
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local fileContents::IOVal<String> =
      readFileT(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
      file_parse(fileContents.iovalue, filename);
  local fileAST::(QName, ListOfCommands) = fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
      processModuleDecl(fileAST.1, import_parse, interface_parse,
                        outerface_parse, fileContents.io);
  local fileErrors::[Message] = fileAST.2.fileErrors;
  --
  local proverState::ProverState = error("compile_file.proverState");
  --
  local compiledContents::String =
        buildCompiledOutput(fileAST.1, fileAST.2, proverState);
  local silverGen::IOVal<String> =
        envVarT("SILVER_GEN", processed.io);
  local outputFile::String =
        silverGen.iovalue ++ substitute(":", "/", fileAST.1.pp) ++
        "/thm_outerface.svthmi";
  local written::IOToken =
        writeFileT(outputFile, compiledContents, silverGen.io);

  return
     if !fileExists.iovalue
     then ioval(printT("Given file " ++ filename ++ " does not exist\n",
                       fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(printT("Syntax error:\n" ++ fileParsed.parseErrors ++
                       "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(printT("Error:  " ++ processed.iovalue.fromLeft ++
                       "\n", processed.io), 1)
     else if !null(fileErrors)
     then ioval(printT("Processing errors:\n" ++
                       implode("\n", map((.pp), fileErrors)) ++ "\n",
                       processed.io), 1)
     else if silverGen.iovalue == ""
     then ioval(printT("Silver generated location not set\n",
                       silverGen.io), 1)
     else ioval(printT("Successfully compiled file " ++ filename ++ "\n",
                       written), 0);
}




function buildCompiledOutput
String ::= currentGrammar::QName comms::ListOfCommands
           proverState::ProverState
{
  return error("buildCompiledOutput");
}

