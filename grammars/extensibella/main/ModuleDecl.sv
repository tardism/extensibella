grammar extensibella:main;


--Read the interface file for a module
function processModuleDecl
IOVal<Either<String
             (ListOfCommands, [DefElement], [ThmElement])>> ::=
   moduleName::QName import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
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
  local parsed_interface::ParseResult<ModuleList_c> =
      interface_parse(interface_file_contents.iovalue,
                      interface_file.iovalue.fromJust);
  local interface::ImportedModuleList =
      parsed_interface.parseTree.ast;

  --Read imported outerface files
  local outerfaceFiles::IOVal<[Either<QName (QName, String)>]> =
      foldr(\ q::QName rest::IOVal<[Either<QName (QName, String)>]> ->
              let mf::IOVal<Maybe<String>> =
                  findFile(q.outerfaceFileName, gen_dirs, rest.io)
              in
                ioval(mf.io, case mf.iovalue of
                             | just(f) -> right((q, f))::rest.iovalue
                             | nothing() -> left(q)::rest.iovalue
                             end)
              end,
            ioval(interface_file_contents.io, []), interface.mods);
  local findOuterfaceFileErrors::[QName] =
      flatMap(\ e::Either<QName (QName, String)> ->
                case e of
                | right(_) -> []
                | left(q) -> [q]
                end, outerfaceFiles.iovalue);
  local outerfaceFilenames::[(QName, String)] =
      flatMap(\ e::Either<QName (QName, String)> ->
                case e of
                | right(p) -> [p]
                | left(_) -> []
                end, outerfaceFiles.iovalue);
  local outerfaces::IOVal<[(QName, Outerface)]> =
      foldr(\ p::(QName, String) rest::IOVal<[(QName, Outerface)]> ->
              let contents::IOVal<String> =
                  readFileT(p.2, rest.io)
              in
              let parsed::ParseResult<Outerface_c> =
                  outerface_parse(contents.iovalue, p.2)
              in
                if !parsed.parseSuccess
                then error("Could not parse outerface file " ++
                        p.2 ++ ":\n" ++ parsed.parseErrors)
                else ioval(contents.io,
                           (p.1, parsed.parseTree.ast)::rest.iovalue)
              end end,
            ioval(outerfaceFiles.io, []), outerfaceFilenames);
  local outerface::([DefElement], [ThmElement]) =
      processModuleOuterfaces(outerfaces.iovalue);

  --Read definition file
  local definition_file::IOVal<Maybe<String>> =
      findFile(moduleName.definitionFileName, gen_dirs,
               outerfaces.io);
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
     --outerface errors
     else if !null(findOuterfaceFileErrors)
     then ioval(outerfaceFiles.io,
             left("Could not find outerface " ++
                (if length(findOuterfaceFileErrors) == 1
                 then "file for module " ++
                      head(findOuterfaceFileErrors).pp
                 else "files for modules " ++
                      implode(", ",
                         map((.pp), findOuterfaceFileErrors))) ++
                "; must compile first"))
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
                right((definition, outerface.1, outerface.2)));
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
      map((.abella_pp), comms.commandList) ++
      map((.abella_pp), flatMap((.encode), defs));
  local back::IOVal<String> =
      sendCmdsToAbella(sendToAbella, abella, ioin, config);
  local parsedOutput::ParseResult<FullDisplay_c> =
      from_parse(back.iovalue, "<<output>>");

  --nothing is known going into this
  comms.typeEnv = [];
  comms.relationEnv = [];
  comms.constructorEnv = [];
  comms.currentModule = error("currentModule not needed?");

  return
     if !parsedOutput.parseSuccess
     then error("Could not parse Abella output:\n\n" ++
                back.iovalue ++ "\n\n" ++ parsedOutput.parseErrors)
     else if parsedOutput.parseTree.ast.isError
     then error("Error passing module specifications to Abella:\n" ++
                parsedOutput.parseTree.ast.pp)
     else ioval(back.io,
                (buildEnv(comms.tys), buildEnv(comms.rels),
                 buildEnv(comms.constrs)));
}
