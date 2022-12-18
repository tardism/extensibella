grammar extensibella:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;
}


--Putting this in a production simplifies the run_step function
abstract production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.pp = "";
}

