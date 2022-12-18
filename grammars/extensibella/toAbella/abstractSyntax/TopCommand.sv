grammar extensibella:toAbella:abstractSyntax;

--import extensibella:thmInterfaceFile:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp;



abstract production extensibleTheoremDeclaration
top::TopCommand ::= depth::Integer thms::[(String, Metaterm, String)]
{
  local join::(String ::= [(String, Metaterm, String)]) =
        \ l::[(String, Metaterm, String)] ->
          case l of
          | [] -> ""
          | [(thm, body, tr)] ->
            thm ++ " : " ++ body.pp ++ " on " ++ tr
          | (thm, body, tr)::t ->
            thm ++ " : " ++ body.pp ++ " on " ++ tr ++ ", " ++ join(t)
          end;
  top.pp = "Extensible_Theorem " ++ join(thms) ++ ".\n";
}


abstract production proveObligations
top::TopCommand ::= names::[String]
{
  top.pp = "Prove " ++ implode(", ", names) ++ ".\n";
}


abstract production theoremDeclaration
top::TopCommand ::= name::String params::[String] body::Metaterm
{
  local buildParams::(String ::= [String]) =
     \ p::[String] ->
       case p of
       | [] ->
         error("Should not reach here; theoremDeclaration production")
       | [a] -> a
       | a::rest ->
         a ++ ", " ++ buildParams(rest)
       end;
  local paramsString::String =
     if null(params)
     then ""
     else " [" ++ buildParams(params) ++ "] ";
  top.pp =
      "Theorem " ++ name ++ " " ++ paramsString ++
      " : " ++ body.pp ++ ".\n";
}


abstract production definitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  local buildPreds::(String ::= [(String, Type)]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; definitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " : " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else buildPreds(preds);
  top.pp = "Define " ++ predsString ++ " by " ++ defs.pp ++ ".";
}


abstract production codefinitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  local buildPreds::(String ::= [(String, Type)]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; codefinitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else buildPreds(preds);
  top.pp = "CoDefine " ++ predsString ++ " by " ++ defs.pp ++ ".";
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";
}


abstract production splitTheorem
top::TopCommand ::= theoremName::String newTheoremNames::[String]
{
  local namesString::String =
     if null(newTheoremNames)
     then ""
     else " as " ++ implode(", ", newTheoremNames);
  top.pp = "Split " ++ theoremName ++ namesString ++ ".\n";
}


--I'm not sure we need new kinds and types declared by the user, but I'll put it in
abstract production kindDeclaration
top::TopCommand ::= names::[String] k::Kind
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(", ", names);
  top.pp = "Kind " ++ namesString ++ "   " ++ k.pp ++ ".\n";
}


abstract production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  local namesString::String =
     if null(names)
     then ""
     else implode(", ", names);
  top.pp = "Type " ++ namesString ++ "   " ++ ty.pp ++ ".\n";
}


abstract production closeCommand
top::TopCommand ::= tys::[Type]
{
  local typesString::String =
     if null(tys)
     then error("Close commands should not be devoid of tyes")
     else implode(", ", map((.pp), tys));
  top.pp = "Close " ++ typesString ++ ".\n";
}

