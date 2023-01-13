grammar extensibella:toAbella:abstractSyntax;

abstract production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.pp = "Translation_Constraint " ++ name.pp ++ " : " ++
           "forall " ++ binds.pp ++ ", " ++ body.pp ++ ".\n";
  top.abella_pp =
      error("translationConstraint.abella_pp should not be accessed");

  production fullName::QName =
      if name.isQualified
      then name
      else addQNameBase(top.currentModule, name.shortName);

  body.boundNames = binds.usedNames;

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
        foldr(\ p::(Maybe<String>, Metaterm) rest::[String] ->
                case p.1 of
                | just(x) -> x::rest
                | nothing() ->
                  makeUniqueNameFromBase("H", rest ++ labels)::rest
                end,
              [], body.premises);

  local transTy::QName =
      case body.premises of
      | (_, translationMetaterm(_, ty, _, _))::_ -> ty
      | _ -> error("Should not access transTy")
      end;
  transTy.typeEnv = top.typeEnv;
  local fullType::TypeEnvItem = transTy.fullType;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared translation constraint name " ++
                    name.pp ++ " does not have correct module " ++
                    "(expected " ++ top.currentModule.pp ++ ")")]
      else [];
  --check there are premises and the first premise is a translation
  top.toAbellaMsgs <-
      case body.premises of
      | [] -> [errorMsg("Translation constraint " ++ name.pp ++
                        " must have premises")]
      | (_, translationMetaterm(_, _, _, _))::_ ->
        [] --any type errors are already identified
      | (_, m)::_ ->
        [errorMsg("First premise in translation constraint " ++
            name.pp ++ " must be a translation; found " ++ m.pp)]
      end;

  top.toAbella =
      [anyTopCommand(theoremDeclaration(fullName, [],
          bindingMetaterm(forallBinder(), binds, body.toAbella))),
       anyProofCommand(introsTactic(introsNames)),
       anyProofCommand(caseTactic(nameHint(head(introsNames)),
          head(introsNames), true))];

  top.provingTheorems = [(fullName, body.thm)];

  --no skips at declaration time, so no during commands
  top.duringCommands = [];

  top.afterCommands = [];
}
