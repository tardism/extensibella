grammar extensibella:common:abstractSyntax;


nonterminal Message with pp, isError;

synthesized attribute isError::Boolean;

abstract production errorMsg
top::Message ::= msg::String
{
  top.pp = "Error:  " ++ msg;

  top.isError = true;
}


abstract production warningMsg
top::Message ::= msg::String
{
  top.pp = "Warning:  " ++ msg;

  top.isError = false;
}


--Because we want to do this a lot of places
function errors_to_string
String ::= msgs::[Message]
{
  return foldr(\ m::Message rest::String -> m.pp ++ "\n" ++ rest,
               "", msgs);
}

