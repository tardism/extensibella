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
      toTermList(map(basicNameTerm, relArgs) ++
                 [basicNameTerm(original)]);
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
                       [basicNameTerm(original),
                        basicNameTerm(translated)]),
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
  top.pp =
      "Prove_Ext_Ind " ++ implode(", ", map((.pp), rels)) ++ ".\n";
  top.abella_pp =
      error("proveExtInd.abella_pp should not be accessed");

  --check for the expected obligation
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | [] -> [errorMsg("No obligations left to prove")]
      | translationConstraintTheorem(q, x, b)::_ ->
        [errorMsg("Expected translation constraint obligation " ++
            q.pp)]
      | extensibleMutualTheoremGroup(thms)::_ ->
        [errorMsg("Expected theorem obligations " ++
            implode(", ", map((.pp), map(fst, thms))))]
      | extIndElement(relInfo)::_ ->
        let expectedNames::[QName] = map(fst, relInfo)
        in
          if setEq(rels, expectedNames)
          then []
          else if subset(rels, expectedNames)
          then let missing::[QName] = removeAll(rels, expectedNames)
               in
                 [errorMsg("Missing relation" ++
                     (if length(missing) == 1 then " " else "s ") ++
                     implode(", ",
                        map((.pp), removeAll(rels, expectedNames))))]
               end
          else if subset(expectedNames, rels)
          then [errorMsg("Too many relations; should not have " ++
                   implode(", ",
                      map((.pp), removeAll(expectedNames, rels))))]
          else [errorMsg("Expected ExtInd obligation" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ", map((.pp), expectedNames)))]
        end
      | _ ->
        error("Should be impossible (proveExtInd.toAbellaMsgs)")
      end;

  local obligations::[(QName, [String], [Term], QName, String, String)] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(r) -> r
      | _ -> error("Not possible")
      end;

  local tempThmName::QName =
      toQName("$$$$$ext_ind_" ++ toString(genInt()));

  --get the environment entry for the relation as well
  local fullRelInfo::[(QName, [String], [Term], QName, String, String,
                       RelationEnvItem)] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            (p.1, p.2, p.3, p.4, p.5, p.6,
             decorate p.1 with {relationEnv=top.relationEnv;}.fullRel),
          obligations);

  --definition of R_{ES}
  local extSizeDef::TopCommand =
      let preds::[(QName, Type)] =
          map(\ p::(QName, [String], [Term], QName, String, String,
                    RelationEnvItem) ->
                (extSizeQName(p.1.sub),
                 foldr1(arrowType,
                        init(p.7.types.toList) ++ --drop prop at end
                        [integerType, nameType(toQName("prop"))])),
              fullRelInfo)
      in
      let defs::[Def] =
          buildExtSizeDef(
             map(\ p::(QName, [String], [Term], QName, String, String,
                       RelationEnvItem) -> (p.1, p.7), fullRelInfo))
      in
        definitionDeclaration(preds,
           foldrLastElem(consDefs, singleDefs, defs))
      end end;

  --definition of R_T
  local transRelDef::TopCommand = todoError("proveExtInd.transRelDef");
  local thmDecl::TopCommand =
      theoremDeclaration(tempThmName, [],
         foldr1(andMetaterm, map(snd, top.provingTheorems)));

  top.duringCommands = todoError("proveExtInd.duringCommands");
  top.afterCommands = todoError("proveExtInd.afterCommands");

  top.toAbella =
      [anyTopCommand(extSizeDef), anyTopCommand(transRelDef),
       anyTopCommand(thmDecl)] ++ todoError("proveExtInd.set-up proof");

  top.provingTheorems =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            (addQNameBase(basicQName(p.1.sub.moduleName),
                          "$extInd_" ++ p.1.shortName),
             let usedVars::[String] =
                 nub([p.5, p.6] ++ p.2 ++ flatMap((.usedNames), p.3))
             in
             let num::String = freshName("N", usedVars)
             in
               bindingMetaterm(forallBinder(),
                  toBindings(num::usedVars),
                  impliesMetaterm(
                     relationMetaterm(extSizeQName(p.1.sub),
                        toTermList(p.3 ++ [basicNameTerm(num)]),
                        emptyRestriction()),
                     relationMetaterm(transRelQName(p.1.sub),
                        toTermList(p.3), emptyRestriction())))
             end end),
          obligations);
}


{-
  Build all the definitional clauses for the extSize version of the
  relations in relInfo
-}
function buildExtSizeDef
[Def] ::= relInfo::[(QName, RelationEnvItem)]
{
  local allRels::[QName] = map(fst, relInfo);
  local pcIndex::Integer = head(relInfo).2.pcIndex;
  --filter out clauses for unknown
  local defList::[([Term], Maybe<Metaterm>)] =
      filter(\ p::([Term], Maybe<Metaterm>) ->
               case elemAtIndex(p.1, pcIndex) of
               | nameTerm(unknownQName(_), _) -> false
               | _ -> true
               end,
             head(relInfo).2.defsList);
  local firstRel::[Def] =
      buildExtSizeClauses(head(relInfo).1, defList, pcIndex, allRels);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel ++ buildExtSizeDef(t)
         end;
}
{-
  Build the clauses for the extSize version of a single relation as
  part of a group of relations (allRels)
-}
function buildExtSizeClauses
[Def] ::= rel::QName defs::[([Term], Maybe<Metaterm>)]
          pcIndex::Integer allRels::[QName]
{
  local extSizeRel::QName = extSizeQName(rel.sub);
  local usedVars::[String] =
      case head(defs) of
      | (tms, just(m)) -> m.usedNames ++ flatMap((.usedNames), tms)
      | (tms, nothing()) -> flatMap((.usedNames), tms)
      end;
  local num::String = freshName("N", usedVars);

  --determine whether this is a rule needing a +1 size
  local isExtRule::Boolean =
      let pc::Term = elemAtIndex(head(defs).1, pcIndex)
      in
      let constr::QName = pc.headConstructor
      in
        !sameModule(rel.moduleName, constr)
      end end;

  --(has extSize premises added, new body)
  local modBody::(Boolean, Metaterm) =
      case head(defs).2 of
      | just(bindingMetaterm(existsBinder(), binds, body)) ->
        let x::([String], Metaterm) =
            buildExtSizeDefBody(body, num, isExtRule,
               binds.usedNames ++ usedVars, allRels)
        in
        let fullBinds::Bindings =
            foldr(addBindings(_, nothingType(), _), binds, x.1)
        in
          (!null(x.1),
           bindingMetaterm(existsBinder(), fullBinds, x.2))
        end end
      | just(m) ->
        let x::([String], Metaterm) =
            buildExtSizeDefBody(m, num, isExtRule, usedVars, allRels)
        in
          if null(x.1)
          then (false, x.2) --should hypothetically be equal to m
          else (true,
                bindingMetaterm(existsBinder(),
                   foldrLastElem(addBindings(_, nothingType(), _),
                      oneBinding(_, nothingType()), x.1),
                   x.2))
        end
      | nothing() -> (false, error("Should not access this half"))
      end;
  local newBody::Metaterm = modBody.2;

  --new arguments:  original args + number
  local finalNumber::Term =
      if modBody.1 --something within is modified
      then basicNameTerm(num)
      else if isExtRule
      then integerToIntegerTerm(1) --1 for this step
      else integerToIntegerTerm(0);
  local newArgs::TermList = toTermList(head(defs).1 ++ [finalNumber]);

  --new def corresponding to first original def
  local hereDef::Def =
      case head(defs).2 of
      | just(_) -> ruleDef(extSizeRel, newArgs, newBody)
      | nothing() -> factDef(extSizeRel, newArgs)
      end;

  return case defs of
         | [] -> []
         | _::tl ->
           hereDef::buildExtSizeClauses(rel, tl, pcIndex, allRels)
         end;
}
{-
  Build the body (not including bindings) of a clause, changing each
  top-level relation to its extSize version and adding the additions
  - finalNumName is the name for the size at the root of the clause
-}
function buildExtSizeDefBody
--(new names, full metaterm body defs)
([String], Metaterm) ::= body::Metaterm finalNumName::String
    isExtRule::Boolean usedNames::[String] allRels::[QName]
{
  local allNames::[String] = finalNumName::usedNames;

  --(names of all size numbers,  modified body)
  local modBody::([String], [Metaterm]) =
      foldr(\ m::Metaterm rest::([String], [Metaterm]) ->
              case m of
              | relationMetaterm(r, t, _) when contains(r, allRels) ->
                let name::String = freshName("N", rest.1 ++ allNames)
                in
                  (name::rest.1,
                   relationMetaterm(extSizeQName(r.sub),
                      toTermList(t.toList ++ [basicNameTerm(name)]),
                      emptyRestriction())::rest.2)
                end
              | _ -> (rest.1, m::rest.2)
              end,
            ([], []), splitMetaterm(body));

  --build a term for addition here
  local addTerm::(Metaterm ::= Term Term Term) =
      \ t1::Term t2::Term result::Term ->
        relationMetaterm(toQName(integerAdditionName),
           toTermList([t1, t2, result]), emptyRestriction());
  --add up all the names in the list
  local sumUp::((String, [String], [Metaterm]) ::= [String]) =
      foldrLastElem(
         \ here::String rest::(String, [String], [Metaterm]) ->
           let name::String =
               freshName("N", rest.2 ++ modBody.1 ++ allNames)
           in
             (name, name::rest.2,
              addTerm(basicNameTerm(here), basicNameTerm(rest.1),
                      basicNameTerm(name))::rest.3)
           end,
         \ here::String -> (here, [], []),
         _);
  --(names of addition results, modified body with additions)
  local allBodyParts::([String], [Metaterm]) =
      case modBody.1 of
      | [] -> ([], modBody.2)
      --more than one
      | h::t when isExtRule -> --sum + 1
        let x::(String, [String], [Metaterm]) = sumUp(h::t)
        in
          (x.2, addTerm(integerToIntegerTerm(1), basicNameTerm(x.1),
                        basicNameTerm(finalNumName))::x.3 ++
                modBody.2)
        end
      | h::y::t ->
        let x::(String, [String], [Metaterm]) = sumUp(y::t)
        in
          (x.2, addTerm(basicNameTerm(h), basicNameTerm(x.1),
                        basicNameTerm(finalNumName))::x.3 ++
                modBody.2)
        end
      | [h] -> --add h = finalNumName to get names right
        ([], [eqMetaterm(basicNameTerm(h),
                 basicNameTerm(finalNumName))] ++ modBody.2)
      end;

  --combine it to get the whole thing as a Metaterm
  local fullBody::Metaterm = foldr1(andMetaterm, allBodyParts.2);
  --all the new names
  local fullNewNameSet::[String] = modBody.1 ++ allBodyParts.1;

  return (fullNewNameSet, fullBody);
}