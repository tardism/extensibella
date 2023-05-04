grammar extensibella:toAbella:abstractSyntax;


abstract production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms
{
  top.pp = "Extensible_Theorem " ++ thms.pp ++ ".\n";
  top.abella_pp =
      error("extensibleTheoremDeclaration.abella_pp should not be accessed");

  production extName::QName =
      if thms.len > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(thms.provingTheorems).1;

  top.toAbella =
      [anyTopCommand(theoremDeclaration(extName, [],
                                        thms.toAbella)),
       anyProofCommand(inductionTactic(noHint(),
                                       thms.inductionNums))] ++
      (if thms.len > 1 then [anyProofCommand(splitTactic())]
                       else []) ++
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm

  top.provingTheorems = thms.provingTheorems;

  top.duringCommands = tail(thms.duringCommands);

  top.afterCommands =
      if thms.len > 1
      then [anyTopCommand(splitTheorem(extName,
                             map(fst, thms.provingTheorems)))]
      else []; --nothing to do after if there is only one being proven

  thms.startingGoalNum =
       if thms.len > 1
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
                     implode(", ", map((.pp), importedIndRels)))]
      else let missing::[QName] =
               removeAll(map(fst, extIndGroup.fromJust),
                         thms.inductionRels)
           in
             if null(missing)
             then []
             else [errorMsg("Ext_Ind group does not include " ++
                            "induction relations " ++
                            implode(", ", map((.pp), missing)))]
           end;
}


abstract production proveObligations
top::TopCommand ::= names::[QName]
{
  top.pp = "Prove " ++ implode(", ", map((.pp), names)) ++ ".\n";
  top.abella_pp =
      error("proveObligations.abella_pp should not be accessed");

  --check for the expected theorems being proven
  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | [] -> [errorMsg("No obligations left to prove")]
      | translationConstraintTheorem(q, x, b)::_ ->
        [errorMsg("Expected translation constraint obligation " ++
            q.pp)]
      | extIndElement(relInfo)::_ ->
        [errorMsg("Expected Ext_Ind obligation for " ++
            implode(", ", map((.pp), map(fst, relInfo))))]
      | extensibleMutualTheoremGroup(thms)::_ ->
        let expectedNames::[QName] = map(fst, thms)
        in
          if setEq(names, expectedNames)
          then []
          else if subset(names, expectedNames)
          then let missing::[QName] = removeAll(names, expectedNames)
               in
                 [errorMsg("Missing mutually-inductive obligation" ++
                    (if length(missing) == 1 then " " else "s ") ++
                    implode(", ",
                       map((.pp), removeAll(names, expectedNames))))]
               end
          else if subset(expectedNames, names)
          then [errorMsg("Too many mutually-inductive obligations;" ++
                   " should not have " ++
                   implode(", ",
                      map((.pp), removeAll(expectedNames, names))))]
          else [errorMsg("Expected inductive obligation" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ", map((.pp), expectedNames)))]
        end
      | _ ->
        error("Should be impossible (proveObligations.toAbellaMsgs)")
      end;

  local obligations::[(QName, Bindings, ExtBody, String)] =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(x) -> x
      | _ -> error("Not possible (proveObligations.obligations)")
      end;

  local thms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, String) rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, rest),
            endExtThms(), obligations);
  thms.startingGoalNum =
       if length(names) > 1
       then [1]
       else []; --only one thm, so subgoals for it are 1, 2, ...
  thms.typeEnv = top.typeEnv;
  thms.relationEnv = top.relationEnv;
  thms.constructorEnv = top.constructorEnv;
  thms.currentModule = top.currentModule;

  production extName::QName =
      if length(names) > 1
      then toQName("$extThm_" ++ toString(genInt()))
      else head(names);

  top.toAbella =
      [anyTopCommand(theoremDeclaration(extName, [],
                                        thms.toAbella)),
       anyProofCommand(inductionTactic(noHint(),
                                       thms.inductionNums))] ++
      (if length(names) > 1 then [anyProofCommand(splitTactic())]
                            else []) ++
      map(anyProofCommand,
          head(thms.duringCommands).2); --intros for first thm

  top.provingTheorems =
      map(\ p::(QName, Bindings, ExtBody, String) -> (p.1, p.3.thm),
          obligations);

  top.duringCommands =
      case head(top.proverState.remainingObligations) of
      | extensibleMutualTheoremGroup(_) -> tail(thms.duringCommands)
      | _ -> [] --shouldn't really be accessed
      end;

  top.afterCommands =
      if length(names) > 1
      then [anyTopCommand(splitTheorem(extName,
                             map(fst, top.provingTheorems)))]
      else []; --nothing to split, so nothing to do
}





nonterminal ExtThms with
   pp, len,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   inductionNums, inductionRels,
   startingGoalNum, duringCommands,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs on ExtThms;

--prefix for the subgoals arising from a theorem
inherited attribute startingGoalNum::SubgoalNum;
--gather indices for induction
synthesized attribute inductionNums::[Integer];
--Relations on which we are doing induction
synthesized attribute inductionRels::[QName];

abstract production endExtThms
top::ExtThms ::=
{
  top.pp = "";

  top.len = 0;

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];

  top.inductionNums = [];
  top.inductionRels = [];

  top.duringCommands = [];
}


abstract production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String rest::ExtThms
{
  top.pp = name.pp ++ " : forall " ++ bindings.pp ++ ", " ++
           body.pp ++ " on " ++ onLabel ++
           if rest.pp == "" then "" else ", " ++ rest.pp;

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
        foldl(\ rest::[String] p::(Maybe<String>, Metaterm) ->
                case p.1 of
                | just(x) -> rest ++ [x]
                | nothing() -> rest ++
                  --using "H" as base triggers an Abella error
                  [freshName("Hyp", rest ++ labels)]
                end,
              [], body.premises);

  top.inductionNums =
      case lookup(onLabel, zipWith(pair, introsNames,
                              range(1, length(introsNames) + 1))) of
      | just(x) -> x::rest.inductionNums
      | nothing() ->
        error("Induction nums:  Did not find " ++ onLabel ++ " in " ++
           "intros names [" ++ implode(", ", introsNames) ++ "]")
      end;
  top.inductionRels =
      case lookup(onLabel, zipWith(pair, introsNames,
                                   map(snd, body.premises))) of
      --premises already has full relations
      | just(relationMetaterm(r, _, _)) -> r::rest.inductionRels
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
                  "theorem " ++ name.pp)]
      | just(relationMetaterm(rel, args, r)) ->
        --need to check the metaterm is built by an extensible relation
        let decRel::Decorated QName with {relationEnv} =
            decorate rel with {relationEnv = top.relationEnv;}
        in
          if !decRel.relFound
          then [] --covered by other errors
          else if decRel.fullRel.isExtensible
          then []
          else [errorMsg("Can only induct on extensible relations " ++
                   "for extensible theorems; " ++
                   decRel.fullRel.name.pp ++ " is not extensible")]
        end
      | just(m) ->
        [errorMsg("Can only induct on extensible relations for " ++
            "extensible theorems, not " ++ m.pp)]
      end;

  --check name is qualified with appropriate module
  top.toAbellaMsgs <-
      if name.isQualified
      then if name.moduleName == top.currentModule
           then []
           else [errorMsg("Declared theorem name " ++ name.pp ++
                    " does not have correct module (expected " ++
                    top.currentModule.pp ++ ")")]
      else [];

  top.provingTheorems = (fullName, body.thm)::rest.provingTheorems;

  rest.startingGoalNum = [head(top.startingGoalNum) + 1];

  local inductionRel::RelationEnvItem =
      case foundLabeledPremise of
      | just(relationMetaterm(rel, _, _)) ->
        decorate rel with {relationEnv = top.relationEnv;}.fullRel
      | _ -> error("Should not access inductionRel")
      end;

  --for the subgoals that should arise, the last digit of the subgoal
  --number and whether we need to prove it
  local expectedSubgoals::[(Integer, Boolean)] =
      foldl(\ thusFar::(Integer, [(Integer, Boolean)]) now::QName ->
              if fullName.moduleName == top.currentModule || --new thm
                 now == top.currentModule --new constr
              then (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, true)])
              else (thusFar.1 + 1, thusFar.2 ++ [(thusFar.1, false)]),
            (1, []), inductionRel.clauseModules).2;
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
              groupedExpectedSubgoals);
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
      if !null(expectedSubgoals) && !last(expectedSubgoals).2 &&
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
      else subgoalDuringCommands ++ rest.duringCommands;
  top.duringCommands =
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
}





nonterminal ExtBody with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises, thm,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs on ExtBody;

--premises should have full version of premise
synthesized attribute premises::[(Maybe<String>, Metaterm)];
--Metaterm underlying the body
synthesized attribute thm::Metaterm;

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;

  top.thm = conc;

  top.toAbella = conc.toAbella;

  conc.boundNames = top.boundNames;

  --take everything from before the final implication
  top.premises =
      map(pair(nothing(), _),
         take(length(conc.splitImplies) - 1, conc.splitImplies));
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = label ++ " : (" ++ m.pp ++ ") -> " ++ rest.pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (just(label), m.full)::rest.premises;

  --labels of the form H<num> cause Abella errors
  top.toAbellaMsgs <-
      if startsWith("H", label) &&
         isDigit(substring(1, length(label), label))
      then [errorMsg("Cannot declare label of form \"H<num>\"")]
      else [];
}


abstract production addBasicExtBody
top::ExtBody ::= m::Metaterm rest::ExtBody
{
  top.pp = (if m.isAtomic then m.pp else "(" ++ m.pp ++ ")") ++
           " -> " ++ rest.pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (nothing(), m.full)::rest.premises;
}
