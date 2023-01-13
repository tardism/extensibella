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
  local modComms::ListOfCommands = processed.iovalue.fromRight.1;
  modComms.typeEnv = [];
  modComms.relationEnv = [];
  modComms.constructorEnv = [];
  modComms.currentModule = fileAST.1;
  local fileErrors::[Message] = fileAST.2.fileErrors;
  --
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(import_parse, processed.io);
  local proverState::ProverState =
      defaultProverState(processed.iovalue.fromRight.3,
         buildEnv(modComms.tys), buildEnv(modComms.rels),
         buildEnv(modComms.constrs), stdLibThms.iovalue.fromRight);
  --
  local compiledContents::String =
      buildCompiledOutput(fileAST.1, fileAST.2, proverState);
  local extensibellaGen::IOVal<String> =
      envVarT("EXTENSIBELLA_GENERATED", stdLibThms.io);
  local outputFile::String =
      extensibellaGen.iovalue ++ fileAST.1.outerfaceFileName;
  local written::IOToken =
      writeFileT(outputFile, compiledContents, extensibellaGen.io);

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
     else if extensibellaGen.iovalue == ""
     then ioval(printT("Extensibella generated location not set\n",
                       extensibellaGen.io), 1)
     else ioval(printT("Successfully compiled file " ++ filename ++ "\n",
                       written), 0);
}




function buildCompiledOutput
String ::= currentModule::QName comms::ListOfCommands
           proverState::ProverState
{
  comms.typeEnv = proverState.knownTypes;
  comms.relationEnv = proverState.knownRels;
  comms.constructorEnv = proverState.knownConstrs;
  comms.proverState = proverState;
  comms.currentModule = currentModule;
  return comms.compiled.pp;
}





synthesized attribute compiled<a>::a;

attribute
   compiled<ListOfCommands>
occurs on ListOfCommands;

aspect production emptyListOfCommands
top::ListOfCommands ::=
{
  top.compiled = emptyListOfCommands();
}


aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.compiled =
      case a.compiled of
      | just(ac) -> addListOfCommands(ac, rest.compiled)
      | nothing() -> rest.compiled
      end;
}



attribute compiled<Maybe<AnyCommand>> occurs on AnyCommand;

aspect production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.compiled =
      case c.compiled of
      | just(x) -> just(anyTopCommand(x))
      | nothing() -> nothing()
      end;
}


aspect production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.compiled = nothing();
}


aspect production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.compiled = nothing();
}


aspect production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.compiled = nothing();
}



attribute compiled<Maybe<TopCommand>> occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.compiled = just(theoremDeclaration(fullName, params, body.full));
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local fullPreds::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            ( if p.1.isQualified
              then p.1
              else addQNameBase(top.currentModule, p.1.shortName),
             decorate p.2 with {typeEnv = top.typeEnv;}.full ),
          preds);
  top.compiled = just(definitionDeclaration(fullPreds, defs.full));
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local fullPreds::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            ( if p.1.isQualified
              then p.1
              else addQNameBase(top.currentModule, p.1.shortName),
             decorate p.2 with {typeEnv = top.typeEnv;}.full ),
          preds);
  top.compiled = just(codefinitionDeclaration(fullPreds, defs.full));
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.compiled = nothing();
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.compiled =
      just(splitTheorem(theoremName.fullRel.name, expandedNames));
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.compiled = nothing();
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.compiled = just(kindDeclaration(newNames, k));
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.compiled = just(typeDeclaration(newNames, ty.full));
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.compiled = error("Should not compile importCommand");
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms
{
  top.compiled = just(extensibleTheoremDeclaration(thms.full));
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  local foundThm::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | extensibleMutualTheoremGroup(thms) ->
                 map(fst, thms) == names
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundThm of
      | [extensibleMutualTheoremGroup(thms)] ->
        just(
           extensibleTheoremDeclaration(
              foldr(\ p::(QName, Bindings, ExtBody, String)
                      rest::ExtThms ->
                      addExtThms(p.1, p.2, p.3, p.4, rest),
                    endExtThms(), thms)))
      | _ ->
        error("Could not identify theorems when compiling prove; " ++
              "file must be checkable before compilation")
      end;
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.compiled =
      just(translationConstraint(fullName, binds, body.full));
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  local foundThm::[ThmElement] =
      filter(
         \ t::ThmElement ->
           case t of
           | translationConstraintTheorem(transName, binds, body) ->
             name == transName
           | _ -> false
           end,
         top.proverState.remainingObligations);
  top.compiled =
      case foundThm of
      | [translationConstraintTheorem(name, binds, body)] ->
        just(translationConstraint(name, binds, body))
      | _ ->
        error("Could not identify constraint when compiling prove;" ++
              " file must be checkable before compilation")
      end;
}
