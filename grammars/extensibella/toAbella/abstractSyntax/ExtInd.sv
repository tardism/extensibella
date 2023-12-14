grammar extensibella:toAbella:abstractSyntax;


abstract production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.pp = text("Ext_Ind ") ++ ppImplode(realLine(),
                                  map(\ d::Document ->
                                        docGroup(nest(9, d)),
                                      body.pps)) ++
           text(".") ++ realLine();
  top.abella_pp = "Ext_Ind " ++ body.abella_pp ++ ".\n";

  top.provingTheorems = [];
  top.provingExtInds = body.extIndInfo;

  top.toAbella =
      [anyTopCommand(extSizeDef), anyTopCommand(transRelDef)] ++
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas);

  local fullRelInfo::[(QName, [String], [Term], QName,
                       String, String, RelationEnvItem)] =
      zipWith(\ p::(QName, [String], [Term], QName, String, String)
                e::RelationEnvItem ->
                (e.name, p.2, p.3, p.4, p.5, p.6, e),
              body.extIndInfo, body.relationEnvItems);

  --definition of R_{ES}
  local extSizeDef::TopCommand =
      buildExtSize(map(fst, fullRelInfo), top.relationEnv);

  --definition of R_T
  local transRelDef::TopCommand =
      buildTransRel(body.extIndInfo, top.relationEnv);

  --lemmas about R_{ES}
  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(QName, [String], [Term], QName, String, String,
                    RelationEnvItem) ->
                buildExtSizeLemmas(p.1, p.2), fullRelInfo);

  --Add these to the known theorems, as they are now proven
  top.newTheorems = extSizeLemmas;

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
                 "induction for relation " ++ justShow(q.pp)), split.1)
      end;
}


nonterminal ExtIndBody with
   pps, abella_pp,
   toAbellaMsgs,
   relations, extIndInfo, relationEnvItems,
   currentModule, typeEnv, constructorEnv, relationEnv;
propagate constructorEnv, relationEnv, typeEnv, currentModule,
          toAbellaMsgs on ExtIndBody;

synthesized attribute relations::[QName];
synthesized attribute extIndInfo::[(QName, [String], [Term],
                                    QName, String, String)];
synthesized attribute relationEnvItems::[RelationEnvItem];

abstract production branchExtIndBody
top::ExtIndBody ::= e1::ExtIndBody e2::ExtIndBody
{
  top.pps = e1.pps ++ e2.pps;
  top.abella_pp = e1.abella_pp ++ ",\n        " ++ e2.abella_pp;

  top.relations = e1.relations ++ e2.relations;

  top.extIndInfo = e1.extIndInfo ++ e2.extIndInfo;

  top.relationEnvItems = e1.relationEnvItems ++ e2.relationEnvItems;
}


abstract production oneExtIndBody
top::ExtIndBody ::= rel::QName relArgs::[String]
                    boundVars::MaybeBindings transArgs::TermList
                    transTy::QName original::String translated::String
{
  top.pps = [ppImplode(text(" "), rel.pp::map(text, relArgs)) ++
             text(" with") ++ line() ++
             nest(3, case boundVars of
                     | justBindings(b) ->
                       text("forall ") ++ ppImplode(text(" "),
                                             b.pps) ++ text(", ")
                     | nothingBindings() -> text("")
                     end ++
                     ppImplode(text(" "), transArgs.pps) ++
                     text(" |{") ++ transTy.pp ++ text("}- ") ++
                       text(original ++ " ~~> " ++ translated))];
  top.abella_pp =
      implode(" ", rel.abella_pp::relArgs) ++ " with " ++
      (case boundVars of
       | justBindings(b) -> "forall " ++ b.abella_pp ++ ", "
       | nothingBindings() -> ""
       end) ++
      transArgs.abella_pp ++ " |{" ++ transTy.abella_pp ++ "}- " ++
      original ++ " ~~> " ++ translated;

  transArgs.boundNames = boundVars.usedNames ++ relArgs;

  top.relations = if rel.relFound then [rel.fullRel.name] else [];

  top.extIndInfo = [(rel, relArgs, transArgs.toList,
                     transTy, original, translated)];

  top.relationEnvItems = if rel.relFound then [rel.fullRel] else [];

  --Check relation is an extensible relation from this module
  top.toAbellaMsgs <-
      if !rel.relFound
      then rel.relErrors
      else if !sameModule(top.currentModule, rel.fullRel.name)
      then [errorMsg("Cannot declare extension induction for " ++
                     "relation " ++ justShow(rel.fullRel.name.pp) ++
                     " not declared in this module")]
      else if !rel.fullRel.isExtensible
      then [errorMsg("Cannot declare extension induction for " ++
               " non-extensible relation " ++
               justShow(rel.fullRel.name.pp))]
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
                      justShow(rel.fullRel.name.pp) ++ "'s primary " ++
                      "component type " ++ justShow(q.pp) ++ " but " ++
                      "found " ++ justShow(transTy.fullType.name.pp))]
           | _ -> error("PC type must be a name")
           end;
  --Check the PC is the one being translated
  top.toAbellaMsgs <-
      if !rel.relFound
      then []
      else if elemAtIndex(relArgs, rel.fullRel.pcIndex) == original
      then []
      else [errorMsg("Must translate primary component of relation" ++
               justShow(rel.pp) ++ " (name " ++
               elemAtIndex(relArgs, rel.fullRel.pcIndex) ++
               ") but found " ++ original)];
  --Check the arguments to the relation are variables (capitalized)
  top.toAbellaMsgs <-
      flatMap(\ x::String ->
                if isCapitalized(x) then []
                else [errorMsg("Arguments to relation " ++
                         justShow(rel.pp) ++
                         " must be capitalized, but found " ++ x)],
              relArgs);
  --Check the translation is a variable (capitalized)
  top.toAbellaMsgs <-
      if isCapitalized(translated) then []
      else [errorMsg("Translation " ++ translated ++
                     " for relation " ++ justShow(rel.pp) ++
                     " must be capitalized")];
  --Check the translation is not in the bound variables
  top.toAbellaMsgs <-
      if contains(translated, boundVars.usedNames)
      then [errorMsg("Translation name " ++ translated ++
               " for relation " ++ justShow(rel.pp) ++
               " should not be included in bound variables")]
      else [];

  --Check it is well-typed
  top.toAbellaMsgs <-
      case unifyTransArgs.upSubst of
      | right(_) -> []
      | left(_) ->
        --given the messages are not terribly useful:
        [errorMsg("Type error in Ext_Ind for " ++ justShow(rel.pp))]
      end;

  --typing
  local relArgTys::[(String, Type)] =
      map(\ x::String ->
            (x, varType("__RelArg" ++ toString(genInt()))),
          relArgs);
  local unifyRelArgs::TypeUnify =
      if rel.relFound && rel.fullRel.isExtensible
      then typeUnify(
              freshenType(
                 foldr1(arrowType, rel.fullRel.types.toList)),
              foldr(arrowType, propType, map(snd, relArgTys)))
      else blankUnify();
  local unifyTransTy::TypeUnify =
      if transTy.typeFound && contains(original, relArgs)
      then typeUnify(nameType(transTy.fullType.name),
              lookup(original, relArgTys).fromJust)
      else blankUnify();
  local unifyTransArgs::TypeUnify =
      if transTy.typeFound
      then typeUnify( --propType for convenience (need if empty)
              foldr(arrowType, propType,
                    transTy.fullType.transTypes.toList),
              foldr(arrowType, propType, transArgs.types.toList))
      else blankUnify();
  transArgs.downVarTys =
      (translated, if transTy.typeFound
                   then nameType(transTy)
                   else varType("__Trans" ++ toString(genInt()))
      )::relArgTys ++
      map(\ p::(String, MaybeType) ->
            (p.1,
             case p.2 of
             | justType(t) -> t
             | nothingType() -> varType("__X" ++ toString(genInt()))
             end), boundVars.toList);
  transArgs.downSubst = emptySubst();
  unifyRelArgs.downSubst = transArgs.upSubst;
  unifyTransTy.downSubst = unifyRelArgs.upSubst;
  unifyTransArgs.downSubst = unifyTransTy.upSubst;
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
  top.pp = ppImplode(text(" "), b.pps);
  top.abella_pp = b.abella_pp;

  top.toList = b.toList;
  top.len = b.len;

  top.usedNames := b.usedNames;
}

abstract production nothingBindings
top::MaybeBindings ::=
{
  top.pp = text("");
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.usedNames := [];
}


abstract production proveExtInd
top::TopCommand ::= rels::[QName]
{
  top.pp = text("Prove_Ext_Ind ") ++ ppImplode(text(",") ++ line(),
                                        map((.pp), rels)) ++
           text(".") ++ realLine();
  top.abella_pp =
      error("proveExtInd.abella_pp should not be accessed");

  --check for the expected obligation
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | [] -> [errorMsg("No obligations left to prove")]
      | translationConstraintTheorem(q, x, b)::_ ->
        [errorMsg("Expected translation constraint obligation " ++
            justShow(q.pp))]
      | extensibleMutualTheoremGroup(thms, alsos)::_ ->
        [errorMsg("Expected theorem obligations " ++
            implode(", ", map(justShow, map((.pp), map(fst, thms)))) ++
            if null(alsos) then ""
            else " also " ++
                 implode(", ", map(justShow, map((.pp), map(fst, alsos)))))]
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
                     implode(", ", map(justShow,
                        map((.pp), removeAll(rels, expectedNames)))))]
               end
          else if subset(expectedNames, rels)
          then [errorMsg("Too many relations; should not have " ++
                   implode(", ", map(justShow,
                      map((.pp), removeAll(expectedNames, rels)))))]
          else [errorMsg("Expected ExtInd obligation" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ",
                             map(justShow, map((.pp), expectedNames))))]
        end
      | _ ->
        error("Should be impossible (proveExtInd.toAbellaMsgs)")
      end;

  local obligations::[(QName, [String], [Term], QName, String, String)] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(r) -> r
      | _ -> error("Not possible (proveExtInd.obligations)")
      end;
  --This should only be accessed if there are no errors
  top.provingExtInds = obligations;

  local tempThmName::QName =
      toQName("$$$$$ext_ind_" ++ toString(genInt()));

  --get the environment entry for the relation as well
  local fullRelInfo::[(QName, [String], [Term], QName, String, String,
                       RelationEnvItem)] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            let rel::RelationEnvItem =
                decorate p.1 with {relationEnv=top.relationEnv;}.fullRel
            in
              (rel.name, p.2, p.3, p.4, p.5, p.6, rel)
            end,
          obligations);

  --definition of R_{ES}
  local extSizeDef::TopCommand =
      buildExtSize(map(fst, obligations), top.relationEnv);

  --definition of R_T
  local transRelDef::TopCommand =
      buildTransRel(obligations, top.relationEnv);

  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(QName, [String], [Term], QName, String, String,
                    RelationEnvItem) ->
                buildExtSizeLemmas(p.1, p.2), fullRelInfo);

  local thmDecl::TopCommand =
      theoremDeclaration(tempThmName, [],
         foldr1(andMetaterm, map(snd, top.provingTheorems)));

  local inductionCommands::[ProofCommand] =
      let numRels::Integer = length(rels)
      in --induction on (acc, extSize)
        [inductionTactic(noHint(), repeat(2, numRels)),
         inductionTactic(noHint(), repeat(1, numRels))]
      end;

  --Add these to the known theorems, as they are now proven
  top.newTheorems = extSizeLemmas;

  --To get the appropriate skips and such for the during commands, we
  --use ExtThms to compute them for us
  local computeDuringCommands::ExtThms =
      foldr(\ p::(QName, [String], [Term], QName, String, String,
                  RelationEnvItem) rest::ExtThms ->
              addExtThms(p.1, --name just needs to have right module
                 oneBinding("", nothingType()), --unneeded for cmds
                 --thm just needs right relations and names for intros
                 addLabelExtBody("Rel",
                    relationMetaterm(p.1, toTermList([]),
                       emptyRestriction()),
                 addLabelExtBody("Acc", trueMetaterm(),
                    endExtBody(trueMetaterm()))),
                 "Rel", nothing(), rest),
            endExtThms(), fullRelInfo);
  computeDuringCommands.startingGoalNum =
      --if only one thm, subgoals for it are 1, 2, ...
      if length(rels) > 1 then [1] else [];
  computeDuringCommands.typeEnv = top.typeEnv;
  computeDuringCommands.relationEnv = top.relationEnv;
  computeDuringCommands.currentModule = top.currentModule;
  computeDuringCommands.constructorEnv = top.constructorEnv;
  computeDuringCommands.useExtInd = []; --none needed here
  computeDuringCommands.shouldBeExtensible = true;
  computeDuringCommands.followingCommands = [];
  --tail because the first one is intros/case for first thm
  top.duringCommands = tail(computeDuringCommands.duringCommands);
  --nothing to do, since we don't need the theorems until composition
  top.afterCommands = [];

  top.toAbella =
      [anyTopCommand(extSizeDef), anyTopCommand(transRelDef)] ++
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas) ++ [anyTopCommand(thmDecl)] ++
      map(anyProofCommand, inductionCommands) ++
      --intros/case for first thm
      map(anyProofCommand,
          head(computeDuringCommands.duringCommands).2);

  top.provingTheorems =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            (extIndThmName(p.1),
             let num::String = freshName("N", p.2)
             in
               bindingMetaterm(forallBinder(),
                  toBindings(num::p.2),
                  impliesMetaterm(
                     relationMetaterm(extSizeQName(p.1.sub),
                        toTermList(map(basicNameTerm, p.2 ++ [num])),
                        emptyRestriction()),
                  impliesMetaterm(
                     relationMetaterm(intStrongInductionRel,
                        toTermList([basicNameTerm(num)]),
                        emptyRestriction()),
                     relationMetaterm(transRelQName(p.1.sub),
                        toTermList(map(basicNameTerm, p.2)),
                        emptyRestriction()))))
             end),
          obligations);
}





{--------------------------------------------------------------------
  Extension Size Definition
 --------------------------------------------------------------------}
{-
  Build the full R_ES definition for the relations in fullRels
-}
function buildExtSize
TopCommand ::= fullRels::[QName] relEnv::Env<RelationEnvItem>
{
  local fullRelInfo::[(QName, RelationEnvItem)] =
      map(\ q::QName ->
            (q, decorate q with {relationEnv=relEnv;}.fullRel),
          fullRels);
  local preds::[(QName, Type)] =
      map(\ p::(QName, RelationEnvItem) ->
            (extSizeQName(p.1.sub),
             foldr1(arrowType,
                    init(p.2.types.toList) ++ --drop prop at end
                    [integerType, propType])),
          fullRelInfo);
  local defs::[Def] = buildExtSizeDef(fullRelInfo, fullRels);
  return definitionDeclaration(preds,
            foldrLastElem(consDefs, singleDefs, defs));
}

{-
  Build all the definitional clauses for the extSize version of the
  relations in relInfo
-}
function buildExtSizeDef
[Def] ::= relInfo::[(QName, RelationEnvItem)] allRels::[QName]
{
  local pcIndex::Integer = head(relInfo).2.pcIndex;
  local defList::[([Term], Maybe<Metaterm>)] = head(relInfo).2.defsList;
  local firstRel::[Def] =
      buildExtSizeClauses(head(relInfo).1, defList, pcIndex, allRels);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel ++ buildExtSizeDef(t, allRels)
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





{--------------------------------------------------------------------
  Translation Version of a Relation Definition
 --------------------------------------------------------------------}
{-
  Build the full R_T relation
-}
function buildTransRel
TopCommand ::= relInfo::[(QName, [String], [Term], QName, String,
                          String)] relEnv::Env<RelationEnvItem>
{
  local fullRelInfo::[(QName, [String], [Term], QName, String, String,
                       RelationEnvItem)] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            let rel::RelationEnvItem =
                decorate p.1 with {relationEnv=relEnv;}.fullRel
            in
              (rel.name, p.2, p.3, p.4, p.5, p.6, rel)
            end,
          relInfo);
  local preds::[(QName, Type)] =
      map(\ p::(QName, [String], [Term], QName, String, String,
                RelationEnvItem) ->
            (transRelQName(p.7.name.sub),
             foldr1(arrowType, p.7.types.toList)),
            fullRelInfo);
  local defs::[Def] =
      buildTransRelDef(fullRelInfo, map(fst, preds));
  return definitionDeclaration(preds,
             foldrLastElem(consDefs, singleDefs, defs));
}

{-
  Build all the definitional clauses for the translation version of
  the relations in relInfo
-}
function buildTransRelDef
[Def] ::= relInfo::[(QName, [String], [Term], QName, String, String,
                     RelationEnvItem)] allRels::[QName]
{
  local r::(QName, [String], [Term], QName, String, String,
            RelationEnvItem) = head(relInfo);
  local pcIndex::Integer = r.7.pcIndex;
  --filter out clauses for unknown
  local defList::[([Term], Maybe<Metaterm>)] =
      filter(\ p::([Term], Maybe<Metaterm>) ->
               case elemAtIndex(p.1, pcIndex) of
               | nameTerm(unknownQName(_), _) -> false
               | _ -> true
               end,
             r.7.defsList);
  local firstRel::[Def] =
      buildTransRelClauses(r.1, defList, r.2, r.3, r.4, r.5, r.6,
                           pcIndex, allRels);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel ++ buildTransRelDef(t, allRels)
         end;
}

{-
  Build the clauses for the translation version of a single relation
  as part of a group of relations (allRels)
-}
function buildTransRelClauses
[Def] ::= rel::QName defs::[([Term], Maybe<Metaterm>)]
          relArgs::[String] transArgs::[Term] transTy::QName
          original::String translated::String
          pcIndex::Integer allRels::[QName]
{
  local transRel::QName = transRelQName(rel.sub);
  local usedVars::[String] =
      case head(defs) of
      | (tms, just(m)) -> m.usedNames ++ flatMap((.usedNames), tms)
      | (tms, nothing()) -> flatMap((.usedNames), tms)
      end;
  --need a fresh version in case translated is already in the rule
  local freshTransName::String = freshName(translated, usedVars);

  --determine whether this is a rule needing a translation
  local isExtRule::Boolean =
      let pc::Term = elemAtIndex(head(defs).1, pcIndex)
      in
      let constr::QName = pc.headConstructor
      in
        !sameModule(rel.moduleName, constr)
      end end;

  --(body should be used, new body)
  local modBody::(Boolean, Metaterm) =
      case head(defs).2 of
      | just(bindingMetaterm(existsBinder(), binds, body)) ->
        let newBody::Metaterm = replaceRelsTransRels(allRels, body)
        in
        let transRelStuff::([String], Metaterm, Metaterm) =
            createTransRelPremises(transRel, head(defs).1, relArgs,
               transArgs, transTy, original, freshTransName, pcIndex,
               freshTransName::usedVars ++ binds.usedNames)
        in
          if isExtRule
          then
             (true,
              bindingMetaterm(existsBinder(),
                 foldr(addBindings(_, nothingType(), _), binds,
                       transRelStuff.1),
                 andMetaterm(transRelStuff.2,
                 andMetaterm(transRelStuff.3, newBody))))
          else --don't add new premises
             (true, bindingMetaterm(existsBinder(), binds, newBody))
        end end
      | just(m) ->
        let newBody::Metaterm = replaceRelsTransRels(allRels, m)
        in
        let transRelStuff::([String], Metaterm, Metaterm) =
            createTransRelPremises(transRel, head(defs).1, relArgs,
               transArgs, transTy, original, freshTransName, pcIndex,
               freshTransName::usedVars)
        in
          if isExtRule
          then
             (true,
              if null(transRelStuff.1)
              then andMetaterm(transRelStuff.2,
                   andMetaterm(transRelStuff.3, newBody))
              else bindingMetaterm(existsBinder(),
                      foldrLastElem(addBindings(_, nothingType(), _),
                         oneBinding(_, nothingType()),
                         transRelStuff.1),
                      andMetaterm(transRelStuff.2,
                      andMetaterm(transRelStuff.3, newBody))))
          else (true, newBody) --don't add new premises
        end end
      | nothing() when isExtRule ->
        let transRelStuff::([String], Metaterm, Metaterm) =
            createTransRelPremises(transRel, head(defs).1, relArgs,
               transArgs, transTy, original, freshTransName, pcIndex,
               freshTransName::usedVars)
        in
          (true,
           if null(transRelStuff.1)
           then andMetaterm(transRelStuff.2, transRelStuff.3)
           else bindingMetaterm(existsBinder(),
                   foldrLastElem(addBindings(_, nothingType(), _),
                      oneBinding(_, nothingType()),
                      transRelStuff.1),
                   andMetaterm(transRelStuff.2, transRelStuff.3)))
        end
      | nothing() -> (false, error("Should not access this half"))
      end;

  local hereDef::Def =
      if modBody.1
      then ruleDef(transRel, toTermList(head(defs).1), modBody.2)
      else factDef(transRel, toTermList(head(defs).1));

  return case defs of
         | [] -> []
         | _::tl -> hereDef::buildTransRelClauses(rel, tl, relArgs,
                                transArgs, transTy, original,
                                translated, pcIndex, allRels)
         end;
}

{-
  Replace all occurrences of rules in rels in the given metaterm with
  their transRel versions
-}
function replaceRelsTransRels
Metaterm ::= allRels::[QName] m::Metaterm
{
  local replaced::[Metaterm] =
      map(\ m::Metaterm ->
            case m of
            | relationMetaterm(r, t, s) when contains(r, allRels) ->
              relationMetaterm(transRelQName(r.sub), t, s)
            | _ -> m
            end,
          splitMetaterm(m));
  return foldr1(andMetaterm, replaced);
}

{-
  Generate the translation and R_T for the translation
  Returns (new bindings, translation, R_T)
-}
function createTransRelPremises
([String], Metaterm, Metaterm) ::=
    transRel::QName actualArgs::[Term] varArgs::[String]
    transArgs::[Term] transTy::QName original::String trans::String
    pcIndex::Integer usedNames::[String]
{
  --replace varArgs with actualArgs in transArgs
  local replacedTransArgs::[Term] =
      safeReplace(transArgs, varArgs, actualArgs);
  --full translation
  local fullTranslation::Metaterm =
      relationMetaterm(transName(transTy),
         toTermList(replacedTransArgs ++
            [elemAtIndex(actualArgs, pcIndex), basicNameTerm(trans)]),
         emptyRestriction());

  --replace only the primary component in the args
  local newArgs::[Term] =
      take(pcIndex, actualArgs) ++
      basicNameTerm(trans)::drop(pcIndex + 1, actualArgs);
  local newRelation::Metaterm =
      relationMetaterm(transRel, toTermList(newArgs),
                       emptyRestriction());

  --new vars:  gather vars in fullTranslation and newRelation, then
  --subtract those from the original args
  local transVars::[String] = fullTranslation.usedNames;
  local relVars::[String] = newRelation.usedNames;
  local alreadyBoundVars::[String] =
      flatMap((.usedNames), actualArgs);
  local newBoundVars::[String] =
      removeAll(nub(alreadyBoundVars), nub(transVars ++ relVars));

  return (newBoundVars, fullTranslation, newRelation);
}





{--------------------------------------------------------------------
  Extension Size Lemmas
 --------------------------------------------------------------------}
{-
  Build the lemmas for using the extension size:
  1. Size is always non-negative
  2. Size is always an integer (is_integer)
  3. ExtSize version implies the relation itself
  The first one is necessary for using our definition of acc.  We
  would not need it if we used nats, but that would lead to problems
  with representing them to the user and showing the difference
  compared to integers.  The second one is for using stdLib theorems
  for addition and less/lesseq.  The last one is so we can use other
  properties of the relation to help us prove Ext_Ind.

  - rel is the relation for which we are defining extSize
  - argNames is the list of (unique) names for the relation arguments
    (does not include size number for extSize)
-}
function buildExtSizeLemmas
[(QName, Metaterm)] ::= rel::QName argNames::[String]
{
  local numName::String = freshName("N", argNames);
  local binds::Bindings = toBindings(argNames ++ [numName]);
  local extSize::Metaterm =
      relationMetaterm(extSizeQName(rel.sub),
         toTermList(map(basicNameTerm, argNames ++ [numName])),
         emptyRestriction());

  --non-neg:  forall \bar{x} n.  extSize \bar{x} n  ->  0 <= n
  local nonNegThmName::QName =
      addQNameBase(rel.moduleName, "ext_ind_pos_" ++ rel.shortName);
  local nonNegThmBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(toQName(integerLessEqName),
               toTermList([integerToIntegerTerm(0),
                           basicNameTerm(numName)]),
               emptyRestriction())));

  --is int:  forall \bar{x} n.  extSize \bar{x} n  ->  is_integer n
  local isIntThmName::QName =
      addQNameBase(rel.moduleName, "ext_ind_is_int_" ++ rel.shortName);
  local isIntThmBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(toQName("is_integer"),
               toTermList([basicNameTerm(numName)]),
               emptyRestriction())));

  --drop:  forall \bar{x} n.  extSize \bar{x} n  ->  R \bar{x}
  local dropExtSizeName::QName =
      addQNameBase(rel.moduleName, "drop_ext_ind_" ++ rel.shortName);
  local dropExtSizeBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction())));

  return [(nonNegThmName, nonNegThmBody),
          (isIntThmName, isIntThmBody),
          (dropExtSizeName, dropExtSizeBody)];
}
