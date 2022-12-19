grammar extensibella:common:abstractSyntax;


nonterminal Message with pp;

abstract production errorMsg
top::Message ::= msg::String
{
  top.pp = "Error:  " ++ msg;
}


abstract production warningMsg
top::Message ::= msg::String
{
  top.pp = "Warning:  " ++ msg;
}


--Because we want to do this a lot of places
function errors_to_string
String ::= msgs::[Message]
{
  return foldr(\ m::Message rest::String -> m.pp ++ "\n" ++ rest,
               "", msgs);
}

