grammar extensibella:composed;

imports extensibella:main:util;
imports extensibella:main;
imports extensibella:extensions:annotatedOutput;

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  return mainProcess(
            allParsers(module_decl_parse, cmd_parse, from_parse,
               file_parse, import_parse, interface_parse,
               outerface_parse), largs, ioin);
}
