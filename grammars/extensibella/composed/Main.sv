grammar extensibella:composed;

imports extensibella:main;

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  return mainProcess(module_decl_parse, cmd_parse, from_parse,
            file_parse, import_parse, interface_parse,
            outerface_parse, largs, ioin);
}
