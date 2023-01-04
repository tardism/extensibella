grammar extensibella:toAbella:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp, abella_pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   newProofState,
   provingTheorems, duringCommands, afterCommands,
   currentModule, typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          toAbellaMsgs on TopCommand;

aspect default production
top::TopCommand ::=
{
  top.duringCommands = [];
  top.afterCommands = [];
}


abstract production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
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
  top.pp = "Theorem " ++ name.pp ++ " " ++ paramsString ++
           " : " ++ body.pp ++ ".\n";
  top.abella_pp = "Theorem " ++ name.abella_pp ++ " " ++
                  paramsString ++ " : " ++ body.abella_pp ++ ".\n";

  production fullName::QName =
      if name.isQualified
      then name
      else addQNameBase(top.currentModule, name.shortName);
  top.toAbella =
      [anyTopCommand(
          theoremDeclaration(fullName, params, body.toAbella))];

  body.boundNames = [];

  --check if name is qualified and has the appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Theorem name " ++ name.pp ++ " does not" ++
                    " have correct module (expected " ++
                    top.currentModule.pp)]
      else [];

  top.provingTheorems = [(fullName, body)];
}


abstract production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local predsString::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else implode(",\n       ", map(\ p::(QName, Type) ->
                                  p.1.pp ++ " : " ++ p.2.pp, preds));
  top.pp = "Define " ++ predsString ++ " by " ++ defs.pp ++ ".";
  local predsString_abella::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else implode(",\n       ",
             map(\ p::(QName, Type) ->
                   p.1.abella_pp ++ " : " ++ p.2.abella_pp, preds));
  top.abella_pp = "Define " ++ predsString_abella ++ " by " ++
                  defs.abella_pp ++ ".";

  production fullNames::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            if p.1.isQualified
            then p
            else (addQNameBase(top.currentModule, p.1.shortName),
                  p.2),
          preds);

  defs.beingDefined = fullNames;

  top.toAbella = error("definitionDeclaration.toAbella");

  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ p::(QName, Type) ->
                if p.1.isQualified
                then if p.1.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared predicate name " ++
                              p.1.pp ++ " does not have correct " ++
                              "module (expected " ++
                              top.currentModule.pp ++ ")")]
                else [], preds);

  top.provingTheorems = [];
}


abstract production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  local predsString::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else implode(",\n       ", map(\ p::(QName, Type) ->
                                  p.1.pp ++ " : " ++ p.2.pp, preds));
  top.pp = "CoDefine " ++ predsString ++ " by " ++ defs.pp ++ ".";
  local predsString_abella::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else implode(",\n       ",
             map(\ p::(QName, Type) ->
                   p.1.abella_pp ++ " : " ++ p.2.abella_pp, preds));
  top.abella_pp = "CoDefine " ++ predsString_abella ++ " by " ++
                  defs.abella_pp ++ ".";

  production fullNames::[(QName, Type)] =
      map(\ p::(QName, Type) ->
            if p.1.isQualified
            then p
            else (addQNameBase(top.currentModule, p.1.shortName),
                  p.2),
          preds);

  defs.beingDefined = fullNames;

  top.toAbella = error("codefinitionDeclaration.toAbella");

  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ p::(QName, Type) ->
                if p.1.isQualified
                then if p.1.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared predicate name " ++
                              p.1.pp ++ " does not have correct " ++
                              "module (expected " ++
                              top.currentModule.pp ++ ")")]
                else [], preds);

  top.provingTheorems = [];
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";
  top.abella_pp = "Query " ++ m.abella_pp ++ ".\n";

  m.boundNames = [];

  top.toAbella = [anyTopCommand(queryCommand(m.toAbella))];

  top.provingTheorems = [];
}


abstract production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  local namesString::String =
     if null(newTheoremNames)
     then ""
     else " as " ++ implode(", ", map((.pp), newTheoremNames));
  top.pp = "Split " ++ theoremName.pp ++ namesString ++ ".\n";
  local namesString_abella::String =
      if null(newTheoremNames)
      then ""
      else " as " ++
           implode(", ", map((.abella_pp), newTheoremNames));
  top.abella_pp = "Split " ++ theoremName.abella_pp ++
                  namesString_abella ++ ".\n";

  top.toAbella =
      [anyTopCommand(splitTheorem(head(thm).1, expandedNames))];
  --
  production thm::[(QName, Metaterm)] =
     findTheorem(theoremName, top.proverState);
  production splitThm::[Metaterm] = splitMetaterm(head(thm).2);
  --Need to add module to given names and make up names for rest
  local qedNewNames::[QName] =
     map(\ q::QName ->
           if q.isQualified
           then q
           else addQNameBase(top.currentModule, q.shortName),
         newTheoremNames);
  local moreNames::[QName] =
      foldr(\ m::Metaterm rest::[QName] ->
              addQNameBase(top.currentModule,
                           theoremName.shortName ++ "_" ++
                           toString(genInt()))::rest,
            [], drop(length(newTheoremNames), splitThm));
  production expandedNames::[QName] = qedNewNames ++ moreNames;

  top.provingTheorems = [];
}


abstract production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.pp = "Close " ++ tys.pp ++ ".\n";
  top.abella_pp = "Close " ++ tys.abella_pp ++ ".\n";

  top.toAbella = error("closeCommand.toAbella");

  top.provingTheorems = [];
}


abstract production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(", ", map((.pp), names));
  top.pp = "Kind" ++ namesString ++ "   " ++ k.pp ++ ".\n";
  local namesString_abella::String =
     if null(names)
     then ""
     else " " ++ implode(", ", map((.abella_pp), names));
  top.abella_pp = "Kind" ++ namesString_abella ++ "   " ++
                  k.pp ++ ".\n";

  top.toAbella = [anyTopCommand(kindDeclaration(newNames, k))];
  production newNames::[QName] =
      map(\ q::QName ->
            if q.isQualified
            then q
            else addQNameBase(top.currentModule, q.shortName),
          names);

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
  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                if q.isQualified
                then if q.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared type name " ++
                              q.pp ++ " does not have correct " ++
                              "module (expected " ++
                              top.currentModule.pp ++ ")")]
                else [], names);

  top.provingTheorems = [];
}


abstract production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  local namesString::String =
     if null(names)
     then ""
     else implode(", ", map((.pp), names));
  top.pp = "Type " ++ namesString ++ "   " ++ ty.pp ++ ".\n";
  local namesString_abella::String =
     if null(names)
     then ""
     else implode(", ", map((.abella_pp), names));
  top.abella_pp = "Type " ++ namesString_abella ++ "   " ++
                  ty.abella_pp ++ ".\n";

  top.toAbella =
      [anyTopCommand(typeDeclaration(newNames, ty.toAbella))];
  production newNames::[QName] =
      map(\ q::QName ->
            if q.isQualified
            then q
            else addQNameBase(top.currentModule, q.shortName),
          names);

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
  --check names are qualified with appropriate module
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                if q.isQualified
                then if q.moduleName == top.currentModule
                     then []
                     else [errorMsg("Declared constructor name " ++
                              q.pp ++ " does not have correct " ++
                              "module (expected " ++
                              top.currentModule.pp ++ ")")]
                else [], names);

  top.provingTheorems = [];
}

