grammar extensibella:interfaceFile:concreteSyntax;

imports extensibella:common:concreteSyntax;
imports extensibella:common:abstractSyntax;

imports extensibella:interfaceFile:abstractSyntax;


closed nonterminal ModuleList_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<ImportedModuleList>;

concrete productions top::ModuleList_c
|
  { top.ast = emptyModuleList(); }
| mod::Qname_t rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), rest.ast); }
| mod::Id_t rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), rest.ast); }
