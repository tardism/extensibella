grammar extensibella:composed;

imports extensibella:main:util;
imports extensibella:main;
imports extensibella:toAbella:abstractSyntax only SetOfParsers;

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  local parsers::SetOfParsers =
      setOfParsers(module_decl_parse, cmd_parse, from_parse,
         file_parse, import_parse, interface_parse, outerface_parse);
  return mainProcess(parsers, largs, ioin);
}
