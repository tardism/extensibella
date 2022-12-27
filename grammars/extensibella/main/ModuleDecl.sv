grammar extensibella:main;


--Read the interface file for a module
function processModuleDecl
IOVal<Either<String
             (ListOfCommands, [DefElement], [ThmElement])>> ::=
   moduleName::QName import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<Interface_c> ioin::IOToken
{
  local extensibella_gen::IOVal<String> =
      envVarT("EXTENSIBELLA_ENCODED", ioin);
  local gen_dirs::[String] = explode(":", extensibella_gen.iovalue);

  --Read interface file
  local interface_file::IOVal<Maybe<String>> =
      findFile(moduleName.interfaceFileName, gen_dirs,
               extensibella_gen.io);
  local interface_file_contents::IOVal<String> =
      readFileT(interface_file.iovalue.fromJust,
                interface_file.io);
  local parsed_interface::ParseResult<Interface_c> =
      interface_parse(interface_file_contents.iovalue,
                      interface_file.iovalue.fromJust);
  local interface::Interface = parsed_interface.parseTree.ast;

  --Read definition file
  local definition_file::IOVal<Maybe<String>> =
      findFile(moduleName.definitionFileName, gen_dirs,
               interface_file_contents.io);
  local definition_file_contents::IOVal<String> =
      readFileT(definition_file.iovalue.fromJust,
                definition_file.io);
  local parsed_definition::ParseResult<ListOfCommands_c> =
      import_parse(definition_file_contents.iovalue,
                   definition_file.iovalue.fromJust);
  local definition::ListOfCommands = parsed_definition.parseTree.ast;

  --put it together
  return
     --interface errors
     if extensibella_gen.iovalue == ""
     then ioval(extensibella_gen.io,
                left("Generated location not set"))
     else if !interface_file.iovalue.isJust
     then ioval(interface_file.io,
                left("Could not find interface file for module " ++
                     moduleName.pp ++ "; must compile module first"))
     else if !parsed_interface.parseSuccess
     then ioval(interface_file_contents.io,
                left("Could not parse interface file for module " ++
                     moduleName.pp ++ ":\n" ++
                     parsed_interface.parseErrors ++ "\n"))
     --definition errors
     else if !definition_file.iovalue.isJust
     then ioval(definition_file.io,
                left("Could not find definition file for module " ++
                     moduleName.pp ++ "; must compile module first"))
     else if !parsed_definition.parseSuccess
     then ioval(definition_file_contents.io,
                left("Could not parse definition file for module " ++
                     moduleName.pp ++ ":\n" ++
                     parsed_definition.parseErrors ++ "\n"))
     --success
     else ioval(definition_file_contents.io,
                right((definition, interface.defElements,
                       interface.thmElements)));
}


--Send the commands from importing module specifications and build
--   the environments
function set_up_abella_module
IOVal<(Env<TypeEnvItem>, Env<RelationEnvItem>,
       Env<ConstructorEnvItem>)> ::=
     currentModule::QName comms::ListOfCommands defs::[DefElement]
     from_parse::Parser<FullDisplay_c>
     abella::ProcessHandle ioin::IOToken config::Decorated CmdArgs
{
  local sendToAbella::[String] = 
        map((.pp), comms.commandList) ++ map((.pp), defs);
  local back::IOVal<String> =
        sendCmdsToAbella(sendToAbella, abella, ioin, config);
  local parsedOutput::ParseResult<FullDisplay_c> =
        from_parse(back.iovalue, "<<output>>");

  return
     if !parsedOutput.parseSuccess
     then error("Could not parse Abella output:\n\n" ++
                back.iovalue ++ "\n\n" ++ parsedOutput.parseErrors)
     else if parsedOutput.parseTree.ast.isError
     then error("Error passing module specifications to Abella")
     else ioval(back.io, (comms.tys, comms.rels, comms.constrs));
}
