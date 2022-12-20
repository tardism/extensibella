grammar extensibella:toAbella:abstractSyntax;

--import extensibella:thmInterfaceFile:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   languageCtx, proverState;
propagate toAbellaMsgs on TopCommand;


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

  top.toAbella = error("extensibleTheoremDeclaration.toAbella");
}


abstract production proveObligations
top::TopCommand ::= names::[String]
{
  top.pp = "Prove " ++ implode(", ", names) ++ ".\n";

  top.toAbella = error("proveObligations.toAbella");
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

  top.toAbella =
      [anyTopCommand(theoremDeclaration(name, params, body.toAbella))];
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

  top.toAbella = error("codefinitionDeclaration.toAbella");
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";

  top.toAbella = [anyTopCommand(queryCommand(m.toAbella))];
}


abstract production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[String]
{
  local namesString::String =
     if null(newTheoremNames)
     then ""
     else " as " ++ implode(", ", newTheoremNames);
  top.pp = "Split " ++ theoremName.pp ++ namesString ++ ".\n";

  top.toAbella =
      [anyTopCommand(splitTheorem(head(thm).1, expandedNames))];
  --
  production thm::[(QName, Metaterm)] =
     findTheorem(theoremName, top.proverState);
  production splitThm::[Metaterm] = splitMetaterm(head(thm).2);
  --Need to add module to given names and make up names for rest
  local qedNewNames::[QName] =
     map(addQNameBase(top.languageCtx.currentModule, _),
         newTheoremNames);
  local moreNames::[QName] =
        foldr(\ m::Metaterm rest::[QName] ->
                addQNameBase(top.languageCtx.currentModule,
                             theoremName.shortName ++ "_" ++
                             toString(genInt()))::rest,
              [], drop(length(newTheoremNames), splitThm));
  --this isn't quite right because it outputs colons
  production expandedNames::[String] =
     map((.pp), qedNewNames ++ moreNames);
}


abstract production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.pp = "Close " ++ tys.pp ++ ".\n";

  top.toAbella = error("closeCommand.toAbella");
}



{-
  We disallow these at the moment because of the difficulties in
  handling them.  It would be difficult to tell the difference between
  an Extensibella-declared type/constructor and one that is part of
  the language.  We would need to check both possibilities for names
  and make sure we didn't treat one as the other.  Since I don't know
  that new types and constructors are needed as part of the proofs
  that you wouldn't include in the language itself, disallowing them
  is sensible.
-}

abstract production kindDeclaration
top::TopCommand ::= names::[String] k::Kind
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(", ", names);
  top.pp = "Kind " ++ namesString ++ "   " ++ k.pp ++ ".\n";

  top.toAbella = [anyTopCommand(kindDeclaration(newNames, k))];
  local newNames::[String] =
     map((.pp),
         map(addQNameBase(top.languageCtx.currentModule, _), names));

  top.toAbellaMsgs <-
      [errorMsg("No new types currently allowed to be defined")];
}


abstract production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  local namesString::String =
     if null(names)
     then ""
     else implode(", ", names);
  top.pp = "Type " ++ namesString ++ "   " ++ ty.pp ++ ".\n";

  top.toAbella =
      [anyTopCommand(typeDeclaration(newNames, ty.toAbella))];
  local newNames::[String] =
     map((.pp),
         map(addQNameBase(top.languageCtx.currentModule, _), names));

  top.toAbellaMsgs <-
      [errorMsg("No new constructors currently allowed to be defined")];
  --If we change and allow this, we need to check the type being
  --built is a type declared by a Kind declaration in Extensibella
  --rather than as part of the language.  Adding productions in
  --Extensibella would not make sense in an extensible language.
}

