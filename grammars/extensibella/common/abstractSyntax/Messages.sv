grammar extensibella:common:abstractSyntax;


nonterminal Message with msg_pp, isError;

synthesized attribute msg_pp::String;
synthesized attribute isError::Boolean;

abstract production errorMsg
top::Message ::= msg::String
{
  top.msg_pp = "Error:  " ++ msg;

  top.isError = true;
}


abstract production warningMsg
top::Message ::= msg::String
{
  top.msg_pp = "Warning:  " ++ msg;

  top.isError = false;
}


--Because we want to do this a lot of places
function errors_to_string
String ::= msgs::[Message]
{
  return foldr(\ m::Message rest::String -> m.msg_pp ++ "\n" ++ rest,
               "", msgs);
}

