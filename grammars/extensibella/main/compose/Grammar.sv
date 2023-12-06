grammar extensibella:main:compose;

imports extensibella:common;
imports extensibella:fromAbella;
imports extensibella:toAbella;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

imports extensibella:main:util;
imports extensibella:main:run;
imports extensibella:main;

imports silver:util:cmdargs;


--New command line flag
synthesized attribute composeFile::Boolean occurs on CmdArgs;
synthesized attribute composeFilename::String occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.composeFile = false;
  top.composeFilename =
      error("Should not access composeFilename when composeFile is false");
}


abstract production composeFlag
top::CmdArgs ::= outputName::String rest::CmdArgs
{
  top.composeFile = true;
  top.composeFilename = outputName;

  forwards to rest;
}



aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <-
     [flagSpec(name="--compose",
               paramString=just("<filename>"),
               help="compose listed files into a single Abella proof",
               flagParser=option(composeFlag))];

  errors <-
     if a.composeFile && null(a.filenames)
     then ["Must give filename(s) with --compose flag"]
     else [];
}
