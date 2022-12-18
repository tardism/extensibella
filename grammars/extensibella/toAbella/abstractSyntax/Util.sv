grammar extensibella:toAbella:abstractSyntax;


--This isn't included in Silver's library for some reason
function capitalizeString
String ::= s::String
{
  return
     if s == ""
     then ""
     else case substring(0, 1, s) of
          | "a" -> "A" | "b" -> "B" | "c" -> "C" | "d" -> "D" | "e" -> "E"
          | "f" -> "F" | "g" -> "G" | "h" -> "H" | "i" -> "I" | "j" -> "J"
          | "k" -> "K" | "l" -> "L" | "m" -> "M" | "n" -> "N" | "o" -> "O"
          | "p" -> "P" | "q" -> "Q" | "r" -> "R" | "s" -> "S" | "t" -> "T"
          | "u" -> "U" | "v" -> "V" | "w" -> "W" | "x" -> "X" | "y" -> "Y"
          | "z" -> "Z" |  _  -> substring(0, 1, s)
          end ++ substring(1, length(s), s);
}




function buildApplication
Term ::= fun::Term args::[Term]
{
  --I'll make this handle degenerate "applications" as well
  return if null(args)
         then fun
         else applicationTerm(fun, buildApplicationArgs(args));
}

function buildApplicationArgs
TermList ::= args::[Term]
{
  return
     case args of
     | [] ->
       error("Should not call buildApplicationArgs with an empty list")
     | [x] -> singleTermList(x)
     | h::t -> consTermList(h, buildApplicationArgs(t))
     end;
}


--Split based on actual conjunctions
--Different than attribute
function splitMetaterm
[Metaterm] ::= mt::Metaterm
{
  return
     case mt of
     | andMetaterm(mt1, mt2) ->
       splitMetaterm(mt1) ++ splitMetaterm(mt2)
     | _ -> [mt]
     end;
}




--Find the metaterm which is the body of a hypothesis
function get_arg_hyp_metaterm
Maybe<Metaterm> ::= arg::ApplyArg hyps::[(String, Metaterm)]
{
  return
     case arg of
     | hypApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     | starApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     end;
}

