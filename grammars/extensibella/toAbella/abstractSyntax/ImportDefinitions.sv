grammar extensibella:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the nonterminals, productions, and attributes declared to build our
  SilverContext.

  We do this in a separate file because the attributes here have to do
  with reading a file, not proving as we see in the other files.

  IMPORTANT:  This will *only* work with module encodings that are
  correctly defined.  If it does not follow the prescribed format, we
  might miss something or add something that is not supposed to be
  added.
-}



nonterminal ListOfCommands with
   pp,
   commandList;

synthesized attribute commandList::[AnyCommand];


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = "";

  top.commandList = [];
}


abstract production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.pp = a.pp ++ rest.pp;

  top.commandList = a::rest.commandList;
}


abstract production joinListOfCommands
top::ListOfCommands ::= l1::ListOfCommands l2::ListOfCommands
{
  top.pp = l1.pp ++ l2.pp;

  top.commandList = l1.commandList ++ l2.commandList;
}
