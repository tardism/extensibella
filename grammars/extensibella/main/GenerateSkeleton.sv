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
      filter((.inSkeleton), processModule.iovalue.fromRight.3);
  local outputString::String =
      "Module " ++ justShow(module.pp) ++ ".\n\n\n" ++
      implode("\n\n\n", map(\ p::ThmElement -> p.skeletonText,
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
      then printT("Writing contents for " ++ justShow(module.pp) ++
                  " into " ++ filename ++ "\n", askReplace.io)
      else printT("Skipping module " ++ justShow(module.pp) ++ "\n",
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



attribute
   inSkeleton, skeletonText
occurs on ThmElement;

--whether it belongs in the generated skeleton
synthesized attribute inSkeleton::Boolean;
--the text to go in the skeleton if it belongs
synthesized attribute skeletonText::String;

aspect production extensibleMutualTheoremGroup
top::ThmElement ::= thms::[(QName, Bindings, ExtBody, String)]
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Prove ") ++
         nest(6, ppImplode(text(",") ++ line(),
                    map((.pp), map(fst, thms)))) ++ text("."));
}


aspect production translationConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
{
  top.inSkeleton = true;
  top.skeletonText = "Prove_Constraint " ++ justShow(name.pp) ++ ".";
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  top.inSkeleton = false;
  top.skeletonText = "";
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.inSkeleton = false;
  top.skeletonText = "";
}


aspect production extIndElement
top::ThmElement ::=
   rels::[(QName, [String], [Term], QName, String, String)]
{
  top.inSkeleton = true;
  top.skeletonText =
      showDoc(80, text("Prove_Ext_Ind ") ++
         ppImplode(text(",") ++ line(), map((.pp), map(fst, rels))) ++
         text("."));
}
