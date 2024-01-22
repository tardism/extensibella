grammar extensibella:main:util;

imports extensibella:common;
imports extensibella:toAbella;
imports extensibella:fromAbella;
imports extensibella:interfaceFile;
imports extensibella:outerfaceFile;

--This is much nicer than the full type:
type Parser<a> = (ParseResult<a> ::= String String);


{-
  In order to have extensible parsers along with extensible actions,
  we have a type to hold them and pass them to actions
-}

attribute
   module_decl_parse, cmd_parse, from_parse, file_parse, import_parse,
   interface_parse, outerface_parse
occurs on SetOfParsers;

synthesized attribute module_decl_parse::Parser<ModuleDecl_c>;
synthesized attribute cmd_parse::Parser<AnyCommand_c>;
synthesized attribute from_parse::Parser<FullDisplay_c>;
synthesized attribute file_parse::Parser<FullFile_c>;
synthesized attribute import_parse::Parser<ListOfCommands_c>;
synthesized attribute interface_parse::Parser<ModuleList_c>;
synthesized attribute outerface_parse::Parser<Outerface_c>;

abstract production setOfParsers
top::SetOfParsers ::=
   module_decl_parse::Parser<ModuleDecl_c>
   cmd_parse::Parser<AnyCommand_c>
   from_parse::Parser<FullDisplay_c>
   file_parse::Parser<FullFile_c>
   import_parse::Parser<ListOfCommands_c>
   interface_parse::Parser<ModuleList_c>
   outerface_parse::Parser<Outerface_c>
{
  top.module_decl_parse = module_decl_parse;
  top.cmd_parse = cmd_parse;
  top.from_parse = from_parse;
  top.file_parse = file_parse;
  top.import_parse = import_parse;
  top.interface_parse = interface_parse;
  top.outerface_parse = outerface_parse;

  forwards to error("Should not forward");
}
