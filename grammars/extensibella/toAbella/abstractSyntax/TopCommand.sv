grammar extensibella:toAbella:abstractSyntax;

--import extensibella:thmInterfaceFile:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   currentModule, typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          toAbellaMsgs on TopCommand;


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
     map(addQNameBase(top.currentModule, _),
         newTheoremNames);
  local moreNames::[QName] =
        foldr(\ m::Metaterm rest::[QName] ->
                addQNameBase(top.currentModule,
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


abstract production kindDeclaration
top::TopCommand ::= names::[String] k::Kind
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(", ", names);
  top.pp = "Kind " ++ namesString ++ "   " ++ k.pp ++ ".\n";

  top.toAbella =
      [anyTopCommand(kindDeclaration(map((.pp), newNames), k))];
  local newNames::[QName] =
        map(addQNameBase(top.currentModule, _), names);

  --redifining a previously-defined type from this module
  top.toAbellaMsgs <-
      foldr(\ q::QName rest::[Message] ->
              case lookupEnv(q, top.typeEnv) of
              | [] -> rest
              | _ ->
                errorMsg("Type " ++ q.pp ++ " already exists " ++
                   "and cannot be defined again")::rest
              end,
            [], newNames);
  --two of the same name in this declaration
  top.toAbellaMsgs <-
      if length(names) == length(nub(names))
      then [] --no duplicates
      else [errorMsg("Cannot declare same type twice")];
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
      [anyTopCommand(typeDeclaration(map((.pp), newNames), ty.toAbella))];
  local newNames::[QName] =
         map(addQNameBase(top.currentModule, _), names);

  --redifining a previously-defined type from this module
  top.toAbellaMsgs <-
      foldr(\ q::QName rest::[Message] ->
              case lookupEnv(q, top.constructorEnv) of
              | [] -> rest
              | _ ->
                errorMsg("Constructor " ++ q.pp ++ " already" ++
                   " exists and cannot be defined again")::rest
              end,
            [], newNames);
  --two of the same name in this declaration
  top.toAbellaMsgs <-
      if length(names) == length(nub(names))
      then [] --no duplicates
      else [errorMsg("Cannot declare same constructor twice")];
}

