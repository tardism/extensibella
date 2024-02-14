grammar extensibella:main:util;

--get the directories where compiled files are placed
function getGenDirs
IOVal<[String]> ::= ioin::IOToken
{
  local extensibella_gen::IOVal<String> =
      envVarT("EXTENSIBELLA_ENCODED", ioin);
  return if extensibella_gen.iovalue == ""
         then error("Generated location not set; " ++
                    "must run Extensibella through given script")
         else ioval(extensibella_gen.io,
                    explode(":", extensibella_gen.iovalue));
}


--look through every directory in dirs for a file named filename
--return full name of first one found (e.g. dir/ect/ory/filename)
function findFile
IOVal<Maybe<String>> ::= filename::String dirs::[String] ioin::IOToken
{
  local fullfile::String = head(dirs) ++ filename;
  local isFile::IOVal<Boolean> = isFileT(fullfile, ioin);
  return case dirs of
         | [] -> ioval(ioin, nothing())
         | _::rest -> if isFile.iovalue
                      then ioval(isFile.io, just(fullfile))
                      else findFile(filename, rest, isFile.io)
         end;
}


{-
  Read a file and produce
  * an error for why it didn't work or
  * (file AST, module information)
-}
function processFile
IOVal<
   Either<String ((Maybe<QName>, ListOfCommands),
                  (ListOfCommands, [DefElement], [ThmElement],
                   [(QName, [QName])]))>> ::=
   filename::String parsers::AllParsers ioin::IOToken
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local fileContents::IOVal<String> =
      readFileT(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
      parsers.file_parse(fileContents.iovalue, filename);
  local fileAST::(Maybe<QName>, ListOfCommands) =
      fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement],
                                        [(QName, [QName])])>> =
      processModuleDecl(fileAST.1.fromJust, parsers, fileContents.io);
  local proc::(ListOfCommands, [DefElement], [ThmElement],
               [(QName, [QName])]) = processed.iovalue.fromRight;

  return
     if !fileExists.iovalue
     then ioval(fileExists.io,
                left("Error:  Given file " ++ filename ++
                     " does not exist\n"))
     else if !fileParsed.parseSuccess
     then ioval(fileContents.io,
             left("Syntax error:\n" ++ fileParsed.parseErrors ++ "\n"))
     else if !fileAST.1.isJust
     then ioval(fileContents.io,
             left("Error:  Module declarations cannot be " ++
                  "Quit in " ++ filename ++ "\n"))
     else if !processed.iovalue.isRight
     then ioval(processed.io,
             left("Error:  " ++ processed.iovalue.fromLeft ++ "\n"))
     else ioval(processed.io,
             right((fileAST, proc.1, proc.2, proc.3, proc.4)));
}


--Produce file names for interface files, definitions, outerface files
synthesized attribute interfaceFileName::String occurs on SubQName, QName;
synthesized attribute outerfaceFileName::String occurs on SubQName, QName;
synthesized attribute definitionFileName::String occurs on SubQName, QName;
synthesized attribute composedFileName::String occurs on SubQName, QName;

aspect production baseName
top::SubQName ::= name::String
{
  top.interfaceFileName = name ++ "___interface.xthmi";
  top.outerfaceFileName = name ++ "___outerface.xthmo";
  top.definitionFileName = name ++ "___definition.thm";
  top.composedFileName = name ++ "___full.thm";
}


aspect production addModule
top::SubQName ::= name::String rest::SubQName
{
  top.interfaceFileName = name ++ ":" ++ rest.interfaceFileName;
  top.outerfaceFileName = name ++ ":" ++ rest.outerfaceFileName;
  top.definitionFileName = name ++ ":" ++ rest.definitionFileName;
  top.composedFileName = name ++ ":" ++ rest.composedFileName;
}



aspect production fixQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production transQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production tyQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production unknownIQName
top::QName ::= rest::QName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production unknownKQName
top::QName ::= rest::QName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production extSizeQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production transRelQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production libQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}


aspect production basicQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
  top.composedFileName = rest.composedFileName;
}
