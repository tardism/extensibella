grammar extensibella:main;


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


--Produce file names for interface files, definitions, outerface files
synthesized attribute interfaceFileName::String occurs on QName;
synthesized attribute outerfaceFileName::String occurs on QName;
synthesized attribute definitionFileName::String occurs on QName;

aspect production baseName
top::QName ::= name::String
{
  top.interfaceFileName = name ++ "___interface.xthmi";
  top.outerfaceFileName = name ++ "___outerface.xthmi";
  top.definitionFileName = name ++ "___definition.thm";
}


aspect production addModule
top::QName ::= name::String rest::QName
{
  top.interfaceFileName = name ++ ":" ++ rest.interfaceFileName;
  top.outerfaceFileName = name ++ ":" ++ rest.outerfaceFileName;
  top.definitionFileName = name ++ ":" ++ rest.definitionFileName;
}
