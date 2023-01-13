grammar extensibella:main;


function generateSkeletonFiles
IOVal<Boolean> ::= gen::[(QName, String)]
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c> ioin::IOToken
{
  local module::QName = head(gen).1;
  local filename::String = head(gen).2;
  --
  local processModule::IOVal<Either<String
                             (ListOfCommands, [DefElement],
                              [ThmElement])>> =
      processModuleDecl(module, import_parse, interface_parse,
         outerface_parse, ioin);
  local outputThms::[ThmElement] =
      filter(\ p::ThmElement ->
               case p of
               | extensibleMutualTheoremGroup(_) -> true
               | translationConstraintTheorem(_, _, _) -> true
               | _ -> false
               end,
             processModule.iovalue.fromRight.3);
  local outputString::String =
      "Module " ++ module.pp ++ ".\n\n\n" ++
      implode("\n\n\n",
         map(\ p::ThmElement ->
               case p of
               | extensibleMutualTheoremGroup(thms) ->
                 "Prove " ++ implode(",\n      ",
                                map((.pp), map(fst, thms))) ++ "."
               | translationConstraintTheorem(name, binds, body) ->
                 "Prove_Constraint " ++ name.pp ++ "."
               | _ -> error("Impossible after filtration")
               end,
             outputThms)) ++ "\n\n";
  --
  local fileExists::IOVal<Boolean> =
      isFileT(filename, processModule.io);
  local askReplace::IOVal<String> =
      if fileExists.iovalue
      then let replace::IOVal<Maybe<String>> =
               readLineStdinT(
                  printT("File " ++ filename ++ " exists; replace? (Y/n) ",
                         fileExists.io))
           in
             ioval(replace.io, replace.iovalue.fromJust)
           end
      else ioval(fileExists.io, "");
  local doOutput::Boolean =
      !fileExists.iovalue ||
      askReplace.iovalue == "" ||
      substring(0, 1, askReplace.iovalue) == "Y" ||
      substring(0, 1, askReplace.iovalue) == "y";
  local message::IOToken =
      if doOutput
      then printT("Writing contents for " ++ module.pp ++ " into " ++
                  filename ++ "\n", askReplace.io)
      else printT("Skipping module " ++ module.pp ++ "\n",
                  askReplace.io);
  local output::IOToken =
      if doOutput
      then writeFileT(filename, outputString, message)
      else message;
  --
  local rest::IOVal<Boolean> =
      generateSkeletonFiles(tail(gen), import_parse, interface_parse,
                            outerface_parse, output);

  return
      case gen of
      | [] -> ioval(ioin, true)
      | hd::tl ->
        case processModule.iovalue of
        | left(err) ->
          ioval(printT("Error:  " ++ err ++ "\n", processModule.io),
                false)
        | right(_) -> rest
        end
      end;
}

