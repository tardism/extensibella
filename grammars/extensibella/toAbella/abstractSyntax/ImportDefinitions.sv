grammar extensibella:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the language information.

  We do this in a separate file because the attributes here have to do
  with reading a file, not proving as we see in the other files.
-}



nonterminal ListOfCommands with
   pp, abella_pp,
   commandList, tys, rels, constrs;

synthesized attribute commandList::[AnyCommand];

synthesized attribute tys::Env<TypeEnvItem>;
synthesized attribute rels::Env<RelationEnvItem>;
synthesized attribute constrs::Env<ConstructorEnvItem>;


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.commandList = [];

  top.tys = error("emptyListOfCommands.tys");
  top.rels = error("emptyListOfCommands.rels");
  top.constrs = error("emptyListOfCommands.constrs");
}


abstract production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.pp = a.pp ++ rest.pp;
  top.abella_pp = a.abella_pp ++ rest.abella_pp;

  top.commandList = a::rest.commandList;

  top.tys = error("addListOfCommands.tys");
  top.rels = error("addListOfCommands.rels");
  top.constrs = error("addListOfCommands.constrs");
}


abstract production joinListOfCommands
top::ListOfCommands ::= l1::ListOfCommands l2::ListOfCommands
{
  top.pp = l1.pp ++ l2.pp;
  top.abella_pp = l1.abella_pp ++ l2.abella_pp;

  top.commandList = l1.commandList ++ l2.commandList;

  top.tys = error("joinListOfCommands.tys");
  top.rels = error("joinListOfCommands.rels");
  top.constrs = error("joinListOfCommands.constrs");
}
