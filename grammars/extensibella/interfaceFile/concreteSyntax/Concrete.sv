grammar extensibella:interfaceFile:concreteSyntax;

imports extensibella:common:concreteSyntax;
imports extensibella:common:abstractSyntax;

imports extensibella:interfaceFile:abstractSyntax;


nonterminal ModuleList_c with ast<ImportedModuleList>;

concrete productions top::ModuleList_c
|
  { top.ast = emptyModuleList(); }
| mod::Qname_t rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), rest.ast); }
