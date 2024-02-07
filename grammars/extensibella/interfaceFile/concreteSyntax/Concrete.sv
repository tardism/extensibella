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
| mod::Qname_t '[' ']' rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), emptyBuildsOnList(),
                            rest.ast); }
| mod::Id_t '[' ']' rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), emptyBuildsOnList(),
                            rest.ast); }
| mod::Qname_t '[' b::BuildsOnModuleList_c ']' rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), b.ast, rest.ast); }
| mod::Id_t '[' b::BuildsOnModuleList_c ']' rest::ModuleList_c
  { top.ast = addModuleList(toQName(mod.lexeme), b.ast, rest.ast); }


closed nonterminal BuildsOnModuleList_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<BuildsOnList>;

concrete productions top::BuildsOnModuleList_c
| mod::Qname_t
  { top.ast = addBuildsOnList(toQName(mod.lexeme),
                              emptyBuildsOnList()); }
| mod::Id_t
  { top.ast = addBuildsOnList(toQName(mod.lexeme),
                              emptyBuildsOnList()); }
| mod::Qname_t ',' rest::BuildsOnModuleList_c
  { top.ast = addBuildsOnList(toQName(mod.lexeme), rest.ast); }
| mod::Id_t ',' rest::BuildsOnModuleList_c
  { top.ast = addBuildsOnList(toQName(mod.lexeme), rest.ast); }
