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
  local fileInfo::
        IOVal<Either<String ((Maybe<QName>, ListOfCommands),
                     (ListOfCommands, [DefElement], [ThmElement]))>> =
      processFile(filename, file_parse, import_parse, interface_parse,
                  outerface_parse, ioin);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileInfo.iovalue.fromRight.1;
  local processed::(ListOfCommands, [DefElement], [ThmElement]) =
      fileInfo.iovalue.fromRight.snd;

  return
     case fileInfo.iovalue of
     | left(err) -> ioval(printT(err, fileInfo.io), 1)
     | right(_) ->
       run(filename, fileAST.2.commandList, import_parse, from_parse,
           fileAST.1.fromJust, processed.1, processed.2, processed.3,
           config, fileInfo.io)
     end;
}
