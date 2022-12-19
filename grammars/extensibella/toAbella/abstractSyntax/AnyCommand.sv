grammar extensibella:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp,
   toAbella<[AnyCommand]>,
   languageCtx, proverState;
propagate languageCtx, proverState on AnyCommand;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.toAbella = c.toAbella;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;

  top.toAbella = map(anyProofCommand, c.toAbella);
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;

  top.toAbella =
      case c.toAbella of
      | nothing() -> []
      | just(n) -> [anyNoOpCommand(n)]
      end;
}


--Putting this in a production simplifies the run_step function
abstract production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.pp = "";

  top.toAbella = [];
}
