grammar extensibella:main:compile;


--Run through a list of files, compiling them
function compile_files
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken
                   config::Configuration
{
  return foldl(\ thusFar::IOVal<Integer> f::String ->
                 if thusFar.iovalue == 0
                 then compile_file(parsers, thusFar.io, f)
                 else thusFar,
               ioval(ioin, 0), config.filenames);
}


--Compile a file, outputting it into the generated directory
function compile_file
IOVal<Integer> ::= parsers::AllParsers ioin::IOToken filename::String
{
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement]))>> =
      processFile(filename, parsers, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement]) =
      fileInfo.iovalue.fromRight.snd;
  --
  local modComms::ListOfCommands = processed.1;
  modComms.typeEnv = [];
  modComms.relationEnv = [];
  modComms.constructorEnv = [];
  modComms.currentModule = fileAST.1.fromJust;
  local fileErrors::[Message] = fileAST.2.fileErrors;
  --
  local stdLibThms::IOVal<Either<String [(QName, Metaterm)]>> =
      importStdLibThms(parsers, fileInfo.io);
  local importedProofDefs::([TypeEnvItem], [RelationEnvItem],
                            [ConstructorEnvItem]) =
      defElementsDefinitions(processed.2);
  local proverState::ProverState =
      defaultProverState(processed.3,
         buildEnv(modComms.tys ++ importedProofDefs.1),
         buildEnv(modComms.rels ++ importedProofDefs.2),
         buildEnv(modComms.constrs ++ importedProofDefs.3),
         stdLibThms.iovalue.fromRight);
  --
  local compiledContents::String =
      buildCompiledOutput(fileAST.1.fromJust, fileAST.2, proverState);
  local extensibellaGen::IOVal<String> =
      envVarT("EXTENSIBELLA_GENERATED", stdLibThms.io);
  local outputFile::String =
      extensibellaGen.iovalue ++ fileAST.1.fromJust.outerfaceFileName;
  local written::IOToken =
      writeFileT(outputFile, compiledContents, extensibellaGen.io);

  return
     case fileInfo.iovalue of
     | left(err) -> ioval(printT(err, fileInfo.io), 1)
     | right(_) ->
       if !null(fileErrors)
       then ioval(printT("Processing errors:\n" ++
                     implode("\n", map((.msg_pp), fileErrors)) ++ "\n",
                     fileInfo.io), 1)
       else if extensibellaGen.iovalue == ""
       then ioval(printT("Extensibella generated location not set\n",
                         extensibellaGen.io), 1)
       else ioval(printT("Successfully compiled file " ++ filename ++
                         "\n", written), 0)
     end;
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
  --use abella_pp to get correct prefixes for relations, types, etc.
  return comms.compiled.abella_pp;
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
        error("Could not identify constraint when compiling " ++
              "Prove_Constraint; file must be checkable before " ++
              "compilation")
      end;
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.compiled = just(extIndDeclaration(body.full));
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName]
{
  local foundExtInd::[ThmElement] =
      filter(\ t::ThmElement ->
               case t of
               | extIndElement(relInfo) ->
                 let l::[QName] = map(fst, relInfo)
                 in --equal by mutual subsets
                   subset(l, rels) && subset(rels, l)
                 end
               | _ -> false
               end,
             top.proverState.remainingObligations);
  top.compiled =
      case foundExtInd of
      | [extIndElement(relInfo)] ->
        just(extIndDeclaration(extIndInfo_to_extIndBody(relInfo)))
      | _ ->
        error("Could not identify Ext_Ind when compiling " ++
              "Prove_Ext_Ind; file must be checkable before " ++
              "compilation")
      end;
}
