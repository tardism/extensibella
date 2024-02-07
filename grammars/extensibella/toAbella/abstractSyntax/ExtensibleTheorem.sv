grammar extensibella:toAbella:abstractSyntax;


abstract production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.pp = text("Extensible_Theorem") ++
           nest(3, realLine() ++ ppImplode(text(",") ++ realLine(),
                                           thms.pps)) ++
           (if alsos.len == 0 then text("")
            else text("also") ++ realLine() ++
                 nest(3, realLine() ++
                         ppImplode(text(",") ++ realLine(),
                                   alsos.pps))) ++
           text(".") ++ realLine();
  --need this for compilation
  top.abella_pp = "Extensible_Theorem " ++ thms.abella_pp ++
      (if alsos.len == 0 then "" else " also " ++ alsos.abella_pp) ++ ".\n";

  production extName::QName =
      if thms.len + alsos.len > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(thms.provingTheorems).1;

  top.toAbella =
      --declare theorems
      [anyTopCommand(theoremDeclaration(extName, [], fullThms)),
      --declare inductions
       anyProofCommand(inductionTactic(noHint(),
                          thms.inductionNums ++ alsos.inductionNums))] ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          thms.renamedIHs ++ alsos.renamedIHs) ++
      --split
      (if thms.len + alsos.len > 1
       then [anyProofCommand(splitTactic())] else []) ++
      --initial set of during commands, which is at least intros
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm
  production fullThms::Metaterm =
      if alsos.len > 0
      then andMetaterm(thms.toAbella, alsos.toAbella)
      else thms.toAbella;

  top.provingTheorems = thms.provingTheorems ++ alsos.provingTheorems;

  top.duringCommands = tail(thms.duringCommands);

  top.afterCommands =
      if thms.len + alsos.len > 1
      then [anyTopCommand(splitTheorem(extName,
               map(fst, thms.provingTheorems ++ alsos.provingTheorems)))]
      else []; --nothing to do after if there is only one being proven

  top.keyRelModules = thms.keyRelModules ++ alsos.keyRelModules;

  thms.startingGoalNum =
       if thms.len + alsos.len > 1
       then [1]
       else []; --only one thm, so subgoals for it are 1, 2, ...

  --find extInd if needed for the relations
  local extIndGroup::Maybe<[(QName, [String], [Term],
                             QName, String, String)]> =
      findExtIndGroup(head(thms.inductionRels), top.proverState);
  --need extInd for all if any relations are imported
  local importedIndRels::[QName] =
      filter(\ r::QName -> !sameModule(top.currentModule, r),
             thms.inductionRels);
  top.toAbellaMsgs <-
      if null(importedIndRels)
      then []
      else if !extIndGroup.isJust
      then [errorMsg("Did not find Ext_Ind required for induction " ++
                     "on relations " ++
                     implode(", ",
                        map(justShow, map((.pp), importedIndRels))))]
      else let missing::[QName] =
               removeAll(map(fst, extIndGroup.fromJust),
                         thms.inductionRels)
           in
             if null(missing)
             then []
             else [errorMsg("Ext_Ind group does not include " ++
                            "induction relations " ++
                            implode(", ",
                               map(justShow, map((.pp), missing))))]
           end;

  --check for naming IH's the same thing
  top.toAbellaMsgs <-
      foldl(\ rest::([(String, String)], [Message])
              p::(String, String, String) ->
              case lookup(p.2, rest.1) of
              | just(thm) ->
                (rest.1, errorMsg("IH name " ++ p.2 ++
                            " already used by " ++ thm)::rest.2)
              | nothing() -> ((p.2, p.3)::rest.1, rest.2)
              end, ([], []), thms.renamedIHs ++ alsos.renamedIHs).2;

  --check for naming thms the same thing
  top.toAbellaMsgs <-
      map(\ q::QName ->
            errorMsg("Theorem " ++ justShow(q.pp) ++ " is declared " ++
                     "multiple times"),
                      --(seen,    multiple)
          foldr(\ q::QName rest::([QName], [QName]) ->
                  if !contains(q, rest.1)
                  then (q::rest.1, rest.2)
                  else if contains(q, rest.2)
                  then (rest.1, rest.2)
                  else (rest.1, q::rest.2),
                ([], []), thms.thmNames ++ alsos.thmNames).2);

  thms.useExtInd = if null(importedIndRels) || !extIndGroup.isJust
                   then []
                   else extIndGroup.fromJust;
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  thms.expectedIHNum = 0;
  thms.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;

  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];
  alsos.startingGoalNum = thms.nextGoalNum;
  alsos.useExtInd = []; --don't need anything here
  alsos.expectedIHNum = thms.len;
  alsos.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
}


abstract production proveObligations
top::TopCommand ::= names::[QName]
{
  top.pp = text("Prove ") ++ nest(6, ppImplode(text(",") ++ line(),
                                        map((.pp), names))) ++
           text(".") ++ realLine();
  top.abella_pp =
      error("proveObligations.abella_pp should not be accessed");

  --check for the expected theorems being proven
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | [] -> [errorMsg("No obligations left to prove")]
      | translationConstraintTheorem(q, x, b)::_ ->
        [errorMsg("Expected translation constraint obligation " ++
            justShow(q.pp))]
      | extIndElement(relInfo)::_ ->
        [errorMsg("Expected Ext_Ind obligation for " ++
            implode(", ", map(justShow, map((.pp), map(fst, relInfo)))))]
      | extensibleMutualTheoremGroup(thms, alsos)::_ ->
        let expectedNames::[QName] = map(fst, thms)
        in
        let expectedAlsoNames::[QName] = map(fst, alsos)
        in
          if setEq(names, expectedNames)
          then []
          else if subset(names, expectedNames)
          then let missing::[QName] = removeAll(names, expectedNames)
               in
                 [errorMsg("Missing mutually-inductive obligation" ++
                    (if length(missing) == 1 then " " else "s ") ++
                    implode(", ", map(justShow,
                       map((.pp), removeAll(names, expectedNames)))))]
               end
          else if subset(expectedNames, names)
          then let extras::[QName] = removeAll(expectedNames, names)
               in
                 if subset(extras, expectedAlsoNames)
                 then [errorMsg("Should not include names for also theorems " ++
                          implode(", ", map(justShow, map((.pp), extras))))]
                 else [errorMsg("Too many mutually-inductive obligations;" ++
                          " should not have " ++
                          implode(", ", map(justShow, map((.pp), extras))))]
               end
          else [errorMsg("Expected inductive obligation" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ", map(justShow,
                                         map((.pp), expectedNames))) ++
                   if null(alsos) then ""
                   else " also " ++
                        implode(", ", map(justShow,
                                          map((.pp), map(fst, alsos)))))]
        end end
      | _ ->
        error("Should be impossible (proveObligations.toAbellaMsgs)")
      end;

  local obligations::[(QName, Bindings, ExtBody, String, Maybe<String>)] =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(x, _) -> x
      | _ -> error("Not possible (proveObligations.obligations)")
      end;
  local alsosInfo::[(QName, Bindings, ExtBody, String, Maybe<String>)] =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(_, x) -> x
      | _ -> error("Not possible (proveObligations.alsos)")
      end;

  local thms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, String, Maybe<String>) rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, p.5, rest),
            endExtThms(), obligations);
  thms.startingGoalNum =
       if length(obligations) + length(alsosInfo) > 1
       then [1]
       else []; --only one thm, so subgoals for it are 1, 2, ...
  thms.typeEnv = top.typeEnv;
  thms.relationEnv = top.relationEnv;
  thms.constructorEnv = top.constructorEnv;
  thms.currentModule = top.currentModule;
  thms.useExtInd = []; --don't need it for Prove
  thms.shouldBeExtensible = true;
  thms.followingCommands = alsos.duringCommands;
  thms.expectedIHNum = 0;
  thms.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;
  local alsos::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, String, Maybe<String>) rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, p.5, rest),
            endExtThms(), alsosInfo);
  alsos.startingGoalNum = thms.nextGoalNum;
  alsos.typeEnv = top.typeEnv;
  alsos.relationEnv = top.relationEnv;
  alsos.constructorEnv = top.constructorEnv;
  alsos.currentModule = top.currentModule;
  alsos.useExtInd = []; --don't need it for alsos
  alsos.shouldBeExtensible = false;
  alsos.followingCommands = [];
  alsos.expectedIHNum = thms.len; --because they start with 0
  alsos.specialIHNames = thms.renamedIHs ++ alsos.renamedIHs;

  production extName::QName =
      if length(names) + alsos.len > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(names);

  top.toAbella =
      --declare theorems
      [anyTopCommand(theoremDeclaration(extName, [], fullThms)),
      --declare inductions
       anyProofCommand(inductionTactic(noHint(),
                          thms.inductionNums ++ alsos.inductionNums))] ++
      --rename IH's
      map(\ p::(String, String, String) ->
            anyProofCommand(renameTactic(p.1, p.2)),
          thms.renamedIHs ++ alsos.renamedIHs) ++
      --split
      (if length(names) + alsos.len > 1
       then [anyProofCommand(splitTactic())]
       else []) ++
      --initial set of during commands, which is at least intros, but
      --   probably also some skips here
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm
  local fullThms::Metaterm =
      if alsos.len > 0
      then andMetaterm(thms.toAbella, alsos.toAbella)
      else thms.toAbella;

  top.provingTheorems =
      map(\ p::(QName, Bindings, ExtBody, String, Maybe<String>) ->
            (p.1, p.3.thm), obligations ++ alsosInfo);

  top.duringCommands =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(_, _) -> tail(thms.duringCommands)
      | _ -> [] --shouldn't really be accessed
      end;

  top.afterCommands =
      if length(names) + length(alsosInfo) > 1
      then [anyTopCommand(splitTheorem(extName,
                             map(fst, top.provingTheorems)))]
      else []; --nothing to split, so nothing to do

  --don't need alsos because we aren't proving them
  top.keyRelModules = thms.keyRelModules;
}





nonterminal ExtThms with
   pps, abella_pp, len,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   inductionNums, inductionRels,
   useExtInd, shouldBeExtensible,
   expectedIHNum, renamedIHs, specialIHNames, thmNames,
   startingGoalNum, nextGoalNum, followingCommands, duringCommands,
   keyRelModules,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs, useExtInd, shouldBeExtensible,
          followingCommands, specialIHNames on ExtThms;

--prefix for the subgoals arising from a theorem
inherited attribute startingGoalNum::SubgoalNum;
--next one afterward
synthesized attribute nextGoalNum::SubgoalNum;
--gather indices for induction
synthesized attribute inductionNums::[Integer];
--Relations on which we are doing induction
synthesized attribute inductionRels::[QName];
--Ext_Ind definition to use for preservability if needed
inherited attribute useExtInd::[(QName, [String], [Term],
                                 QName, String, String)];
--commands following this set of ExtThms
inherited attribute followingCommands::[(SubgoalNum, [ProofCommand])];
--whether the theorem is expected to be extensible
inherited attribute shouldBeExtensible::Boolean;
--the number the IH should be (0 for "IH")
inherited attribute expectedIHNum::Integer;
--new names for IH for various theorems (old name, new name, thm name)
synthesized attribute renamedIHs::[(String, String, String)];
--special names for IH to check they don't interfere with labels
inherited attribute specialIHNames::[(String, String, String)];
--thm names used
synthesized attribute thmNames::[QName];

abstract production endExtThms
top::ExtThms ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.len = 0;

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];

  top.inductionNums = [];
  top.inductionRels = [];

  top.duringCommands = top.followingCommands;

  top.keyRelModules = [];

  top.renamedIHs = [];

  top.nextGoalNum = top.startingGoalNum;

  top.thmNames = [];
}


abstract production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String asName::Maybe<String> rest::ExtThms
{
  top.pps = (name.pp ++ text(" : forall ") ++
             ppImplode(text(" "), bindings.pps) ++ text(",") ++
             nest(3, realLine() ++ body.pp) ++ realLine() ++
             text("on " ++ onLabel) ++
             if asName.isJust then text(" as " ++ asName.fromJust)
                              else text(""))::rest.pps;
  top.abella_pp =
      name.abella_pp ++ " : forall " ++ bindings.abella_pp ++ ", " ++
      body.abella_pp ++ " on " ++ onLabel ++
      (if asName.isJust then " as " ++ asName.fromJust else "") ++
      if rest.abella_pp == "" then "" else ", " ++ rest.abella_pp;

  top.len = 1 + rest.len;

  production fullName::QName =
      if name.isQualified
      then name
      else addQNameBase(top.currentModule, name.shortName);

  top.toAbella =
      case rest of
      | endExtThms() ->
        bindingMetaterm(forallBinder(), bindings, body.toAbella)
      | _ ->
        andMetaterm(
           bindingMetaterm(forallBinder(), bindings, body.toAbella),
           rest.toAbella)
      end;

  body.boundNames = bindings.usedNames;

  production labels::[String] = catMaybes(map(fst, body.premises));
  --names we're going to use for the intros command for this theorem
  local introsNames::[String] =
      generateExtIntrosNames(labels, body.premises);

  top.inductionNums =
      case lookup(onLabel, zip(introsNames,
                              range(1, length(introsNames) + 1))) of
      | just(x) -> x::rest.inductionNums
      | nothing() ->
        error("Induction nums:  Did not find " ++ onLabel ++ " in " ++
           "intros names [" ++ implode(", ", introsNames) ++ "]")
      end;
  top.inductionRels =
      case lookup(onLabel, zip(introsNames,
                                   map(snd, body.premises))) of
      | just(relationMetaterm(r, _, _)) ->
        if inductionRelFound
        then inductionRel.name::rest.inductionRels
        else rest.inductionRels --bad rel, so just check rest
      --bad form, so no relation and just check rest
      | just(_) -> rest.inductionRels
      --no such premise, so just check rest
      | nothing() -> rest.inductionRels
      end;

  --the premise we declared for induction
  local foundLabeledPremise::Maybe<Metaterm> =
      lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                 a.isJust && b.isJust && a.fromJust == b.fromJust,
               just(onLabel), body.premises);
  top.toAbellaMsgs <-
      case foundLabeledPremise of
      | nothing() ->
        [errorMsg("Unknown label " ++ onLabel ++ " in extensible " ++
                  "theorem " ++ justShow(name.pp))]
      | just(relationMetaterm(rel, args, r)) ->
        --need to check the metaterm is built by an extensible relation
        let decRel::Decorated QName with {relationEnv} =
            decorate rel with {relationEnv = top.relationEnv;}
        in
          if !decRel.relFound
          then [] --covered by other errors
          else if top.shouldBeExtensible
             --should be an extensible theorem
          then if !inductionRel.isExtensible
               then [errorMsg("Can only induct on extensible relations " ++
                        "for extensible theorem " ++ justShow(name.pp) ++
                        "; " ++ justShow(inductionRel.name.pp) ++
                        " is not extensible")]
               else case head(drop(inductionRel.pcIndex, args.toList)) of
                    | nameTerm(q, _) when !q.isQualified -> [] --var
                    | _ -> --anything else is structured
                      [errorMsg("Primary component of induction " ++
                          "relation cannot be filled but is in theorem " ++
                          justShow(name.pp))]
                    end ++
                    --check for ExtInd
                    if sameModule(top.currentModule, inductionRel.name)
                    then [] --don't need one
                    else case thisExtInd of
                         | just(_) -> [] --found
                         | nothing() ->
                           [errorMsg("Cannot find ExtInd for relation " ++
                               justShow(inductionRel.name.pp) ++
                               " for extensible theorem " ++ justShow(name.pp))]
                         end
             --should NOT be an extensible theorem
          else if inductionRel.isExtensible
               then [errorMsg("Cannot induct on extensible relations " ++
                        "for non-extensible theorem " ++ justShow(name.pp) ++
                        "; " ++ justShow(inductionRel.name.pp) ++
                        " is extensible")]
               else []
        end
      | just(m) when top.shouldBeExtensible ->
        [errorMsg("Can only induct on extensible relations for " ++
            "extensible theorem " ++ justShow(name.pp) ++
            ", not " ++ justShow(m.pp))]
      | _ -> [] --not extensible, so whatever is allowable
      end;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared theorem name " ++ justShow(name.pp) ++
                    " does not have correct module (expected " ++
                    justShow(top.currentModule.pp) ++ ")")]
      else [];
  --check there are no existing theorems with this full name
  top.toAbellaMsgs <-
      if null(findTheorem(fullName, top.proverState))
      then []
      else [errorMsg("Theorem named " ++ justShow(fullName.pp) ++
                     " already exists")];

  --check the body is well-typed
  top.toAbellaMsgs <-
      case body.upSubst of
      | right(_) ->
        if any(map(\ v::String ->
                     substituteTy(varType(v), body.upSubst).containsVars,
                     allTyVars))
        then [errorMsg("Cannot determine types of all bound " ++
                       "variables in " ++ justShow(name.pp))]
        else []
      | left(errs) ->
        map(add_message_tag(_, "Type error in " ++ justShow(name.pp)), errs)
      end;
  --all type variables in the body
  local allTyVars::[String] =
      body.tyVars ++
      flatMap(\ p::(String, Either<Type String>) ->
                case p.2 of
                | left(_) -> []
                | right(s) -> [s]
                end,
              boundVarTys);
  --save the names for var types here
  local boundVarTys::[(String, Either<Type String>)] =
      map(\ p::(String, MaybeType) ->
            (p.1, case p.2 of
                  | justType(t) -> left(t)
                  | nothingType() ->
                    right("__Bound" ++ toString(genInt()))
                  end),
          bindings.toList);
  body.downVarTys =
      map(\ p::(String, Either<Type String>) ->
            (p.1, case p.2 of
                  | left(t) -> t
                  | right(s) -> varType(s)
                  end),
          boundVarTys);
  body.downSubst = emptySubst();

  top.provingTheorems = (fullName, body.thm)::rest.provingTheorems;

  rest.startingGoalNum = [head(top.startingGoalNum) + 1];

  local inductionRelFound::Boolean =
      case foundLabeledPremise of
      | just(relationMetaterm(rel, _, _)) ->
        decorate rel with {relationEnv = top.relationEnv;}.relFound
      | _ -> false
      end;
  local inductionRel::RelationEnvItem =
      case foundLabeledPremise of
      | just(relationMetaterm(rel, _, _)) ->
        decorate rel with {relationEnv = top.relationEnv;}.fullRel
      | _ -> error("Should not access inductionRel")
      end;

  {-
   - Preservability for imported relations requires us to add the
     translation assertion manually, which we do here
   - Because the PC has to be a variable, the rule for preservability
     will always apply, so we don't need to check if it unifies
   - This outer list is actually a maybe, but easier to add to others
  -}
  local preservabilityAssert::[(Integer, [ProofCommand])] =
      if sameModule(top.currentModule, fullName) && --new prop
         inductionRelFound && --not a relation error
         !sameModule(top.currentModule, inductionRel.name) --old rel 
      then let subgoalNum::Integer =
               last(expectedSubgoals).1 --last number is preservability
           in
           let prems::[String] = catMaybes(map(fst, body.premises))
           in
           let transHyp1::String = freshName(onLabel, prems)
           in
           let transHyp2::String = freshName(onLabel, transHyp1::prems)
           in
               --clear (0 = 0 -> false)
           let clearImpossible::ProofCommand =
               clearCommand([transHyp1], false)
           in
               --move (R Trans *) to transHyp1
           let renameSub::ProofCommand =
               renameTactic(transHyp2, transHyp1)
           in
               --put (|{ty}- <unknown ty> ~~> Trans) in transHyp2
           let assertTrans::ProofCommand =
               assertTactic(nameHint(transHyp2), nothing(),
                  translation)
           in
             [(subgoalNum, [clearImpossible, renameSub,
                            assertTrans, skipTactic()])]
           end end end end end end end
      else []; --nothing to do if not new prop/imported rel
  --
  local thisExtInd::Maybe<(QName, [String], [Term],
                           QName, String, String)> =
      if inductionRelFound --guard against out-of-order access
      then case lookup(inductionRel.name, top.useExtInd) of
           | just(p) -> just((inductionRel.name, p))
           | nothing() -> nothing()
           end
      else nothing();
  --
  local propUsedNames::[String] = body.thm.usedNames;
  --It is named "Trans" in the definition file, so it will have either
  --that name or a fresh version of it, if something else uses that
  local translationName::String = freshName("Trans", propUsedNames);
  local transArgs::[Term] =
      safeReplace(thisExtInd.fromJust.3, thisExtInd.fromJust.2,
         case foundLabeledPremise of
         | just(relationMetaterm(_, args, _)) -> args.toList
         | _ -> [] --shouldn't access
         end);
  local translation::Metaterm =
      relationMetaterm(transName(thisExtInd.fromJust.4),
         toTermList(transArgs ++
                    [nameTerm(unknownIQName(thisExtInd.fromJust.4.sub),
                              nothingType()),
                     basicNameTerm(translationName)]),
         emptyRestriction());

  local relArgs::[Term] =
      case foundLabeledPremise of
      | just(relationMetaterm(_, a, _)) -> a.toList
      | _ -> [] --should not need in this case
      end;

  --for the subgoals that should arise, the last digit of the subgoal
  --number and whether we need to prove it
  local expectedSubgoals::[(Integer, Boolean)] =
      if !inductionRelFound then [] --guard against out-of-order access
      else
      foldl(
         \ thusFar::(Integer, [(Integer, Boolean)])
           now::([Term], Maybe<Metaterm>) ->
           let pc::Term =
               elemAtIndex(now.1, inductionRel.pcIndex)
           in
           let pcMod::QName =
               if decorate pc with {
                     relationEnv = top.relationEnv;
                     constructorEnv = top.constructorEnv;
                  }.isStructured
               then pc.headConstructor.moduleName
               else inductionRel.name.moduleName
           in
             if unifyTermsSuccess(now.1, relArgs) --rule applies
             then if fullName.moduleName == top.currentModule || --new thm
                     pcMod == top.currentModule --new constr
                  then (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, true)])
                  else (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, false)])
             else thusFar --doesn't apply:  just continue with next
           end end,
         (1, []), inductionRel.defsList).2;
  --group consecutive skips
  local groupedExpectedSubgoals::[[(Integer, Boolean)]] =
      groupBy(\ p1::(Integer, Boolean) p2::(Integer, Boolean) ->
                p1.2 == p2.2,
              expectedSubgoals);
  --last digit of subgoal and skips needed
  local subgoalDurings::[(Integer, [ProofCommand])] =
      flatMap(\ l::[(Integer, Boolean)] ->
                if !null(l) && !head(l).2 --things we don't do we skip
                then [(head(l).1,
                       map(\ x::(Integer, Boolean) ->
                             skipTactic(), l))]
                else [], --nothing for things we need to prove
              groupedExpectedSubgoals) ++ preservabilityAssert;
  --turned into full subgoals
  local subgoalDuringCommands::[(SubgoalNum, [ProofCommand])] =
      map(\ p::(Integer, [ProofCommand]) ->
            (top.startingGoalNum ++ [p.1], p.2),
          subgoalDurings);
  {-
    The first thing in ExtThm.duringCommands is always for the first
    subgoal for the goal because we need intros.  If we skip the last
    subgoal here, we need to add the starting commands from the next
    to the last group of commands here.
  -}
  local combinedCommands::[(SubgoalNum, [ProofCommand])] =
      if top.shouldBeExtensible
      then if !null(expectedSubgoals) && !last(expectedSubgoals).2 &&
              !null(rest.duringCommands) && !null(subgoalDuringCommands)
           then let lastSubgoal::(SubgoalNum, [ProofCommand]) =
                    last(subgoalDuringCommands)
                in
                  take(length(subgoalDuringCommands) - 1,
                       subgoalDuringCommands) ++
                  [(lastSubgoal.1,
                    lastSubgoal.2 ++ head(rest.duringCommands).2)] ++
                  tail(rest.duringCommands)
                end
           else subgoalDuringCommands ++ rest.duringCommands
      else rest.duringCommands;
  top.duringCommands =
      if top.shouldBeExtensible
      then extensibleDuringCommands
      else alsoDuringCommands;
  --during commands for an extensible theorem, where we do case and
  --   may not have any subgoals after that
  local extensibleDuringCommands::[(SubgoalNum, [ProofCommand])] =
      --intros and case immediately
      [(top.startingGoalNum,
        [introsTactic(introsNames),
         caseTactic(nameHint(onLabel), onLabel, true)] ++
         --add first group of skips if they happen right away
         (if !null(combinedCommands) && !null(subgoalDurings) &&
             head(subgoalDurings).1 == 1
          then head(combinedCommands).2
          else []))] ++
      if !null(combinedCommands) && !null(subgoalDurings) &&
          head(subgoalDurings).1 == 1
      then tail(combinedCommands)
      else combinedCommands;
  --during commands for a non-extensible theorem, where we do not do
  --   case automatically and thus must have a subgoal to solve
  local alsoDuringCommands::[(SubgoalNum, [ProofCommand])] =
      if fullName.moduleName == top.currentModule
         --new theorem:  solve, intros immediately
      then [(top.startingGoalNum, [introsTactic(introsNames)])] ++
           combinedCommands
         --imported theorem:  skip it
      else if !null(combinedCommands)
           then (top.startingGoalNum,
                 skipTactic()::head(combinedCommands).2)::tail(combinedCommands)
           else [(top.startingGoalNum, [skipTactic()])];

  top.keyRelModules =
      (top.startingGoalNum, inductionRel.name.moduleName)::rest.keyRelModules;

  --can't name IH to something that might be an Abella-generated IH name
  top.toAbellaMsgs <-
      case asName of
      | nothing() -> []
      | just(n) ->
        if matches_IH_form(n)
        then [errorMsg("Cannot have IH name in as clause of form \"IH<num>\"")]
        else []
      end;
  top.renamedIHs =
      case asName of
      | nothing() -> []
      | just(n) when top.expectedIHNum == 0 -> [("IH", n, name.shortName)]
      | just(n) -> [("IH" ++ toString(top.expectedIHNum), n, name.shortName)]
      end ++ rest.renamedIHs;

  --next number
  rest.expectedIHNum = top.expectedIHNum + 1;

  --pass it up
  top.nextGoalNum = rest.nextGoalNum;
  top.thmNames = fullName::rest.thmNames;
}

--generate names for intros
--must be determined entirely by arguments (no using genInt())
function generateExtIntrosNames
[String] ::= knownLabels::[String]
             premiseInfo::[(Maybe<String>, Metaterm)]
{
  return
      foldl(\ rest::[String] p::(Maybe<String>, Metaterm) ->
              case p.1 of
              | just(x) -> rest ++ [x]
              | nothing() -> rest ++
                --using "H" as base triggers an Abella error
                [freshName("Hyp", rest ++ knownLabels)]
              end,
            [], premiseInfo);
}





nonterminal ExtBody with
   pp, abella_pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises, thm,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState,
   upSubst, downSubst, downVarTys, tyVars,
   specialIHNames;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs,
          downVarTys, tyVars, specialIHNames on ExtBody;

--premises should have full version of premise
synthesized attribute premises::[(Maybe<String>, Metaterm)];
--Metaterm underlying the body
synthesized attribute thm::Metaterm;

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;
  top.abella_pp = conc.abella_pp;

  top.thm = conc;

  top.toAbella = conc.toAbella;

  conc.boundNames = top.boundNames;

  --take everything from before the final implication
  top.premises =
      map(\ a -> (nothing(), a),
         take(length(conc.splitImplies) - 1, conc.splitImplies));

  conc.downSubst = top.downSubst;
  top.upSubst = conc.upSubst;
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = text(label ++ " : ") ++
           (if m.isAtomic then m.pp else parens(m.pp))++
           text(" ->") ++ realLine() ++ rest.pp;
  top.abella_pp =
      label ++ " : (" ++ m.abella_pp ++ ") -> " ++ rest.abella_pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (just(label), m)::rest.premises;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  --labels of the form H<num> cause Abella errors
  top.toAbellaMsgs <-
      if startsWith("H", label) &&
         isDigit(substring(1, length(label), label))
      then [errorMsg("Cannot declare label of form \"H<num>\"")]
      else [];
  --labels of the form IH<num> may interfere with inductive hypotheses
  top.toAbellaMsgs <-
      if matches_IH_form(label)
      then [errorMsg("Cannot declare label of form \"IH<num>\"")]
      else [];
  --cannot have names of
  top.toAbellaMsgs <-
      let whichThm::Maybe<String> =
          lookup(label, map(snd, top.specialIHNames))
      in
        case whichThm of
        | nothing() -> []
        | just(thm) ->
          [errorMsg("Label " ++ label ++ " is the name of the IH " ++
                    "for " ++ thm ++ " and cannot be used as a " ++
                    "premise label")]
        end
      end;
}


abstract production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.pp = (if m.isAtomic then m.pp else parens(m.pp)) ++
           text(" ->") ++ realLine() ++ rest.pp;
  top.abella_pp =
      (if m.isAtomic then m.abella_pp else "(" ++ m.abella_pp ++ ")") ++
      " -> " ++ rest.abella_pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (nothing(), m.full)::rest.premises;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;
}




--check if it is IH[0-9]*
function matches_IH_form
Boolean ::= n::String
{
  return startsWith(n, "IH") && isDigit(substring(2, length(n), n));
}
