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
synthesized attribute interfaceFileName::String occurs on SubQName, QName;
synthesized attribute outerfaceFileName::String occurs on SubQName, QName;
synthesized attribute definitionFileName::String occurs on SubQName, QName;

aspect production baseName
top::SubQName ::= name::String
{
  top.interfaceFileName = name ++ "___interface.xthmi";
  top.outerfaceFileName = name ++ "___outerface.xthmi";
  top.definitionFileName = name ++ "___definition.thm";
}


aspect production addModule
top::SubQName ::= name::String rest::SubQName
{
  top.interfaceFileName = name ++ ":" ++ rest.interfaceFileName;
  top.outerfaceFileName = name ++ ":" ++ rest.outerfaceFileName;
  top.definitionFileName = name ++ ":" ++ rest.definitionFileName;
}



aspect production fixQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
}


aspect production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
}


aspect production transQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
}


aspect production tyQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
}


aspect production basicQName
top::QName ::= rest::SubQName
{
  top.interfaceFileName = rest.interfaceFileName;
  top.outerfaceFileName = rest.outerfaceFileName;
  top.definitionFileName = rest.definitionFileName;
}
