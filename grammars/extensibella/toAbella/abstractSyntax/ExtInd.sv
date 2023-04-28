grammar extensibella:toAbella:abstractSyntax;


abstract production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.pp = "Ext_Ind " ++ body.pp ++ ".\n";
  top.abella_pp =
      error("extIndDeclaration.abella_pp should not be accessed");

  top.provingTheorems = [];

  top.toAbella =
      [anyTopCommand(
          definitionDeclaration(
             map(\ p::(QName, Type, Def) -> (p.1, p.2), body.toAbella),
             foldr(consDefs, singleDefs(head(body.toAbella).3),
                   map(\ p::(QName, Type, Def) -> p.3,
                       tail(body.toAbella)))))];

  --Check each relation occurs at most once
  top.toAbellaMsgs <- --([duplicated], [seen])
      let split::([QName], [QName]) =
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if contains(q, rest.2) && !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), body.relations)
      in
        map(\ q::QName ->
              errorMsg("Duplicate definitions of extension " ++
                 "induction for relation " ++ q.pp), split.1)
      end;
}


nonterminal ExtIndBody with
   pp,
   toAbella<[(QName, Type, Def)]>, toAbellaMsgs,
   relations,
   currentModule, typeEnv, constructorEnv, relationEnv;
propagate constructorEnv, relationEnv, typeEnv, currentModule,
          toAbellaMsgs on ExtIndBody;

synthesized attribute relations::[QName];

abstract production branchExtIndBody
top::ExtIndBody ::= e1::ExtIndBody e2::ExtIndBody
{
  top.pp = e1.pp ++ ",\n        " ++ e2.pp;

  top.toAbella = e1.toAbella ++ e2.toAbella;

  top.relations = e1.relations ++ e2.relations;
}


abstract production oneExtIndBody
top::ExtIndBody ::= rel::QName relArgs::[String]
                    boundVars::MaybeBindings transArgs::TermList
                    transTy::QName original::String translated::String
{
  top.pp = implode(" ", rel.pp::relArgs) ++ " with " ++
           (case boundVars of
            | justBindings(b) -> "forall " ++ b.pp ++ ", "
            | nothingBindings() -> ""
            end) ++
           transArgs.pp ++ " |{" ++ transTy.pp ++ "}- " ++
           original ++ " ~~> " ++ translated;

  transArgs.boundNames = boundVars.usedNames ++ relArgs;

  top.relations = if rel.relFound then [rel.fullRel.name] else [];

  {-
    This "translation" seems a bit strange, and it is unrelated to
    anything.  However, we don't have any actual work to do here, as
    the actual definitions and proof requirements aren't required in
    the introducing module.  That would allow us to have a blank
    translation, but we don't have typing defined, so we need to check
    the types of transArgs make sense.  This random-looking definition
    lets us do that.
  -}
  top.toAbella = [(testRelQName, testRelTy,
                   ruleDef(testRelQName, testRelArgs, testRelBody))];
  local testRelName::String = "$$$ext_ind_test_def_" ++ rel.shortName;
  local testRelQName::QName = toQName(testRelName);
  local testRelTy::Type = --rel tys, transTy
      foldr(arrowType, nameType(toQName("prop")),
            init(rel.fullRel.types.toList) ++ --drop ending prop
            transTy.fullType.transTypes.toList ++
            [nameType(transTy.fullType.name)]);
  local testRelArgs::TermList = --relArgs, orig, trans
      toTermList(map(\ x::String ->
                       nameTerm(toQName(x), nothingType()), relArgs) ++
                 [nameTerm(toQName(original), nothingType())]);
  local testRelBody::Metaterm =
      bindingMetaterm(existsBinder(),
         case boundVars of
         | justBindings(b) ->
           addBindings(translated, nothingType(), b)
         | nothingBindings() ->
           oneBinding(translated, nothingType())
         end,
         --transArgs |- original ~~> translated
         relationMetaterm(transQName(transTy.fullType.name.sub),
            toTermList(transArgs.toList ++
                       [nameTerm(toQName(original), nothingType()),
                        nameTerm(toQName(translated), nothingType())]),
            emptyRestriction()));

  --Check relation is an extensible relation from this module
  top.toAbellaMsgs <-
      if !rel.relFound
      then rel.relErrors
      else if !sameModule(top.currentModule, rel.fullRel.name)
      then [errorMsg("Cannot declare extension induction for " ++
                     "relation " ++ rel.fullRel.name.pp ++
                     " not declared in this module")]
      else if !rel.fullRel.isExtensible
      then [errorMsg("Cannot declare extension induction for " ++
               " non-extensible relation " ++ rel.fullRel.name.pp)]
      else [];
  --Check ty exists and the translation translates the right type
  top.toAbellaMsgs <-
      if !transTy.typeFound
      then transTy.typeErrors
      else if !rel.relFound 
      then []
      else case rel.fullRel.pcType of
           | nameType(q) ->
             if q == transTy.fullType.name
             then []
             else [errorMsg("Translation must be for relation " ++
                      rel.fullRel.name.pp ++ "'s primary component" ++
                      " type " ++ q.pp ++ " but found " ++
                      transTy.fullType.name.pp)]
           | _ -> error("PC type must be a name")
           end;
  --Check the PC is the one being translated
  top.toAbellaMsgs <-
      if !rel.relFound
      then []
      else if elemAtIndex(relArgs, rel.fullRel.pcIndex) == original
      then []
      else [errorMsg("Must translate primary component of relation" ++
               rel.pp ++ " (name " ++
               elemAtIndex(relArgs, rel.fullRel.pcIndex) ++
               ") but found " ++ original)];
  --Check the arguments to the relation are variables (capitalized)
  top.toAbellaMsgs <-
      flatMap(\ x::String ->
                if isCapitalized(x) then []
                else [errorMsg("Arguments to relation " ++ rel.pp ++
                         " must be capitalized, but found " ++ x)],
              relArgs);
  --Check the translation is a variable (capitalized)
  top.toAbellaMsgs <-
      if isCapitalized(translated) then []
      else [errorMsg("Translation " ++ translated ++
                     " for relation " ++ rel.pp ++
                     " must be capitalized")];
  --Check the translation is not in the bound variables
  top.toAbellaMsgs <-
      if contains(translated, boundVars.usedNames)
      then [errorMsg("Translation name " ++ translated ++
               " for relation " ++ rel.pp ++
               " should not be included in bound variables")]
      else [];
}


nonterminal MaybeBindings with
   pp, abella_pp,
   toList<(String, MaybeType)>, len,
   usedNames,
   typeEnv;
propagate typeEnv on MaybeBindings;

abstract production justBindings
top::MaybeBindings ::= b::Bindings
{
  top.pp = b.pp;
  top.abella_pp = b.abella_pp;

  top.toList = b.toList;
  top.len = b.len;

  top.usedNames := b.usedNames;
}

abstract production nothingBindings
top::MaybeBindings ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.usedNames := [];
}


abstract production proveExtInd
top::TopCommand ::= rels::[QName]
{
  top.pp = "Prove_Ext_Ind " ++ implode(", ", map((.pp), rels)) ++ ".\n";
  top.abella_pp =
      error("proveExtInd.abella_pp should not be accessed");

  top.toAbella = todoError("proveExtInd.toAbella");

  top.provingTheorems = todoError("proveExtInd.provingTheorems");
}
