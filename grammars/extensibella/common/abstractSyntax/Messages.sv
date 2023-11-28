grammar extensibella:common:abstractSyntax;


nonterminal Message with msg_pp, isError, addTag, tagged;

synthesized attribute msg_pp::String;
synthesized attribute isError::Boolean;

--add an extra tag to the string message within a message
inherited attribute addTag::String;
synthesized attribute tagged::Message;

abstract production errorMsg
top::Message ::= msg::String
{
  top.msg_pp = "Error:  " ++ msg;

  top.isError = true;

  top.tagged = errorMsg(top.addTag ++ ": " ++ msg);
}


abstract production warningMsg
top::Message ::= msg::String
{
  top.msg_pp = "Warning:  " ++ msg;

  top.isError = false;

  top.tagged = warningMsg(top.addTag ++ ": " ++ msg);
}


--Because we want to do this a lot of places
function errors_to_string
String ::= msgs::[Message]
{
  return foldr(\ m::Message rest::String -> m.msg_pp ++ "\n" ++ rest,
               "", msgs);
}


--Add a tag easily to any type of message
function add_message_tag
Message ::= m::Message tag::String
{
  m.addTag = tag;
  return m.tagged;
}
