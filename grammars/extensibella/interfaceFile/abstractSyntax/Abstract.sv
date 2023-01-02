grammar extensibella:interfaceFile:abstractSyntax;

imports extensibella:common:abstractSyntax;

nonterminal ImportedModuleList with mods;

synthesized attribute mods::[QName];

abstract production emptyModuleList
top::ImportedModuleList ::=
{
  top.mods = [];
}


abstract production addModuleList
top::ImportedModuleList ::= module::QName rest::ImportedModuleList
{
  top.mods = module::rest.mods;
}
