grammar extensibella:toAbella:abstractSyntax;


abstract production extIndDeclaration
top::TopCommand ::= rel::QName relArgs::[String]
                    boundVars::MaybeBindings transArgs::TermList
                    transTy::QName original::String translated::String
{
  top.pp = "Ext_Ind " ++ implode(" ", rel.pp::relArgs) ++ " with " ++
           (case boundVars of
            | justBindings(b) -> "forall " ++ b.pp ++ ", "
            | nothingBindings() -> ""
            end) ++
           transArgs.pp ++ " |{" ++ transTy.pp ++ "}- " ++
           original ++ " ~~> " ++ translated ++ ".\n";
  top.abella_pp =
      error("extIndDeclaration.abella_pp should not be accessed");

  top.provingTheorems = [];

  transArgs.boundNames = boundVars.usedNames ++ relArgs;

  {-
    This "translation" seems a bit strange, and it is unrelated to
    anything.  However, we don't have any actual work to do here, as
    the actual definitions and proof requirements aren't required in
    the introducing module.  That would allow us to have a blank
    translation, but we don't have typing defined, so we need to check
    the types of transArgs make sense.  This random-looking definition
    lets us do that.
  -}
  top.toAbella =
      [anyTopCommand(
          definitionDeclaration([(testRelQName, testRelTy)],
             singleDefs(ruleDef(testRelQName, testRelArgs,
                                testRelBody))))];
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
               " (name " ++ elemAtIndex(relArgs, rel.fullRel.pcIndex) ++
               ") but found " ++ original)];
  --Check the arguments to the relation are variables (capitalized)
  top.toAbellaMsgs <-
      flatMap(\ x::String ->
                if isCapitalized(x) then []
                else [errorMsg("Arguments to relation must be " ++
                               "capitalized, but found " ++ x)],
              relArgs);
  --Check the translation is a variable (capitalized)
  top.toAbellaMsgs <-
      if isCapitalized(translated) then []
      else [errorMsg("Translation " ++ translated ++
                     " must be capitalized")];
  --Check the translation is not in the bound variables
  top.toAbellaMsgs <-
      if contains(translated, boundVars.usedNames)
      then [errorMsg("Translation name " ++ translated ++
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
top::TopCommand ::= rel::QName
{
  top.pp = "Prove_Ext_Ind " ++ rel.pp ++ ".\n";
  top.abella_pp =
      error("proveExtInd.abella_pp should not be accessed");

  top.toAbella = todoError("proveExtInd.toAbella");

  top.provingTheorems = todoError("proveExtInd.provingTheorems");
}
