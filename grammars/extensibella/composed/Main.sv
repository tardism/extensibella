grammar extensibella:composed;

imports extensibella:main:util;
imports extensibella:main;
imports extensibella:extensions:annotatedOutput;

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  local parsers::SetOfParsers =
      setOfParsers(module_decl_parse, cmd_parse, from_parse,
         file_parse, import_parse, interface_parse, outerface_parse);
  return mainProcess(parsers, largs, ioin);
}
