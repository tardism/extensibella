grammar extensibella:toAbella:abstractSyntax;


abstract production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.pp = text("Ext_Ind ") ++ ppImplode(text(";") ++ realLine(),
                                  map(\ d::Document ->
                                        docGroup(nest(9, d)),
                                      body.pps)) ++
           text(".") ++ realLine();
  top.abella_pp = "Ext_Ind " ++ body.abella_pp ++ ".\n";

  top.provingTheorems = [];
  top.provingExtInds = body.extIndInfo;

  body.startingGoalNum =
      if body.len > 1
      then [1]
      else []; --only one, so subgoals are 1, 2, ...

  local extIndName::String = "$Ext_Ind_" ++ toString(genInt());
  top.toAbella =
      --relation definition
      [anyTopCommand(transRelDef)] ++
       --declare theorem
      [anyTopCommand(theoremDeclaration(toQName(extIndName), [],
                        body.toAbella))] ++
       --declare inductions:  acc (if using ExtSize) and rel
      (if useExtSize
       then [anyProofCommand(inductionTactic(noHint(), repeat(2, body.len)))]
       else []) ++
      [anyProofCommand(inductionTactic(noHint(), repeat(1, body.len)))] ++
       --split
      (if body.len > 1 then [anyProofCommand(splitTactic())]
                       else []) ++
       --initial set of during commands, which is at least intros
      map(anyProofCommand, head(body.duringCommands).2);

  body.downDuringCommands = [];
  top.duringCommands = tail(body.duringCommands);

  local fullRelInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                       RelationEnvItem)] =
      zipWith(\ p::(QName, [String], Bindings, ExtIndPremiseList)
                e::RelationEnvItem ->
                (e.name, p.2, p.3, p.4, e),
              body.extIndInfo, body.relationEnvItems);

  --whether or not to use ExtSize for the proof, or just the relation
  local useExtSize::Boolean =
      case fullRelInfo of
      | [] -> true
      | (q, _, _, _, _)::rest ->
        case findExtSizeGroup(q, top.proverState) of
        | nothing() -> false
        | just(g) -> subset(map(fst, rest), g)
        end
      end;
  body.useExtSize = useExtSize;

  --definition of R_T
  local transRelDef::TopCommand =
      buildTransRel(body.extIndInfo, top.relationEnv);

  top.newTheorems = [];

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
  --Check no relation has a pre-existing ExtInd
  top.toAbellaMsgs <-
      flatMap(\ q::QName ->
                case findExtIndGroup(q, top.proverState) of
                | just(_) ->
                  [errorMsg("Pre-existing ExtInd for " ++
                      justShow(q.pp) ++ "; cannot redefine it")]
                | nothing() -> []
                end,
              body.relations);
  --Check if the relations have ExtSize and have it together
  --Not an error, but something possibly unintended, so warn
  top.toAbellaMsgs <-
      if useExtSize
      then []
      else [warningMsg("No definition of Ext Size for all " ++
               "relations in Ext Ind; defaulting to proving " ++
               "Ext Ind without Ext Size")];
}


nonterminal ExtIndBody with
   pps, abella_pp,
   len,
   proverState,
   toAbella<Metaterm>, toAbellaMsgs,
   useExtSize,
   downDuringCommands, duringCommands, startingGoalNum, nextGoalNum,
   relations, extIndInfo, relationEnvItems,
   currentModule, typeEnv, constructorEnv, relationEnv;
propagate constructorEnv, relationEnv, typeEnv, currentModule,
          toAbellaMsgs, useExtSize, proverState on ExtIndBody;

synthesized attribute relations::[QName];
                --[(rel, args, total bound vars, premises)]
synthesized attribute extIndInfo::[(QName, [String], Bindings,
                                    ExtIndPremiseList)];
synthesized attribute relationEnvItems::[RelationEnvItem];
--thread commands around, since we might need to combine them
inherited attribute downDuringCommands::[(SubgoalNum, [ProofCommand])];
--whether to use ExtSize in thm statement, or just relation itself
inherited attribute useExtSize::Boolean;

abstract production branchExtIndBody
top::ExtIndBody ::= e1::ExtIndBody e2::ExtIndBody
{
  top.pps = e1.pps ++ e2.pps;
  top.abella_pp = e1.abella_pp ++ ";\n        " ++ e2.abella_pp;

  top.len = e1.len + e2.len;

  top.relations = e1.relations ++ e2.relations;

  top.extIndInfo = e1.extIndInfo ++ e2.extIndInfo;

  top.relationEnvItems = e1.relationEnvItems ++ e2.relationEnvItems;

  e1.startingGoalNum = top.startingGoalNum;
  e2.startingGoalNum = e1.nextGoalNum;
  top.nextGoalNum = e2.nextGoalNum;

  e2.downDuringCommands = top.downDuringCommands;
  e1.downDuringCommands = e2.duringCommands;
  top.duringCommands = e1.duringCommands;

  top.toAbella = andMetaterm(e1.toAbella, e2.toAbella);
}


abstract production oneExtIndBody
top::ExtIndBody ::= boundVars::Bindings rel::QName relArgs::[String]
                    premises::ExtIndPremiseList
{
  top.pps = [text("forall ") ++ ppImplode(text(" "), boundVars.pps) ++
             text(", ") ++
             ppImplode(text(" "), rel.pp::map(text, relArgs)) ++
             if premises.len > 0
             then ( text(" with") ++ line() ++
                    nest(3, ppImplode(text(", "), premises.pps)) )
             else text("")];
  top.abella_pp =
      "forall " ++ boundVars.abella_pp ++ ", " ++
      implode(" ", rel.abella_pp::relArgs) ++
      if premises.len > 0
      then (" with " ++ premises.abella_pp)
      else "";

  top.len = 1;

  local fullRel::RelationEnvItem = rel.fullRel;

  premises.boundNames = boundVars.usedNames ++ relArgs;

  top.relations = if rel.relFound then [fullRel.name] else [];

  top.extIndInfo = [(if rel.relFound then fullRel.name else rel,
                     relArgs, boundVars, premises)];

  top.relationEnvItems = if rel.relFound then [fullRel] else [];

  top.nextGoalNum = [head(top.startingGoalNum) + 1];

  local givenLabels::[String] = filterMap(fst, premises.toList);
  local relLabel::String = freshName("R", givenLabels);
  local introsNames::[String] =
      [relLabel] ++
      (if top.useExtSize then [freshName("Acc", givenLabels)]
                         else []) ++
      map(fromMaybe("_", _), map(fst, premises.toList)); 

  --[(last element of subgoal number, whether to prove it)]
  local expectedSubgoals::[(Integer, Boolean)] =
      if !rel.relFound
      then [] --no cases without known relation
      else foldl(\ thusFar::(Integer, [(Integer, Boolean)])
                   now::([Term], Maybe<Metaterm>) ->
                   let pc::Term =
                       elemAtIndex(now.1, fullRel.pcIndex)
                   in
                   let pcMod::QName =
                       if decorate pc with {
                             relationEnv = top.relationEnv;
                             constructorEnv = top.constructorEnv;
                          }.isStructured
                       then pc.headConstructor.moduleName
                       else fullRel.name.moduleName
                   in
                     (thusFar.1 + 1,
                      thusFar.2 ++ [(thusFar.1,
                                     pcMod == top.currentModule)])
                   end end,
                 (1, []), fullRel.defsList).2;
  --group consecutive skips
  local groupedExpectedSubgoals::[[(Integer, Boolean)]] =
      groupBy(\ p1::(Integer, Boolean) p2::(Integer, Boolean) ->
                p1.2 == p2.2, expectedSubgoals);
  --last element of subgoal and skips needed
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
  --combine with the first one of downDuringCommands if we skip the
  --   last thing here
  local combinedCommands::[(SubgoalNum, [ProofCommand])] =
      if !null(expectedSubgoals) && !last(expectedSubgoals).2 &&
         !null(top.downDuringCommands) && !null(subgoalDuringCommands)
      then let lastSubgoal::(SubgoalNum, [ProofCommand]) =
               last(subgoalDuringCommands)
           in
             init(subgoalDuringCommands) ++
             [(lastSubgoal.1,
               lastSubgoal.2 ++ head(top.downDuringCommands).2)] ++
             tail(top.downDuringCommands)
           end
      else subgoalDuringCommands ++ top.downDuringCommands;

  top.duringCommands =
      [(top.startingGoalNum,
        [introsTactic(introsNames),
         caseTactic(nameHint(relLabel), relLabel, true)] ++
        --add first skips if they happen right away
        (if !null(combinedCommands) && !null(subgoalDurings) &&
            head(subgoalDurings).1 == 1
         then head(combinedCommands).2
         else []))] ++
      --add rest of during commands, dropping head if we took it
      if !null(combinedCommands) && !null(subgoalDurings) &&
         head(subgoalDurings).1 == 1
      then tail(combinedCommands)
      else combinedCommands;

  top.toAbella = buildExtIndThm(boundVars.toAbella, rel.fullRel.name,
                    relArgs, premises.toAbella, top.useExtSize);

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
  --Check the arguments to the relation are variables (capitalized)
  top.toAbellaMsgs <-
      flatMap(\ x::String ->
                if isCapitalized(x) then []
                else [errorMsg("Arguments to relation " ++
                         justShow(rel.pp) ++
                         " must be capitalized, but found " ++ x)],
              relArgs);
  --Check the arguments to the relation are unique
  top.toAbellaMsgs <-
      if length(relArgs) != length(nub(relArgs))
      then [errorMsg("Arguments to " ++ justShow(rel.pp) ++
               " must be unique variables; found duplicates")]
      else [];
  --Check names given to premises are unique
  top.toAbellaMsgs <-
      foldr(\ x::String rest::([String], [Message]) ->
              if contains(x, rest.1)
              then (rest.1,
                    errorMsg("Repeated premise name " ++ x ++
                       " for relation " ++ justShow(rel.pp))::rest.2)
              else (x::rest.1, rest.2),
            ([], []), filterMap(fst, premises.toList)).2;

  --Check it is well-typed
  top.toAbellaMsgs <-
      case unifyRelArgs.upSubst of
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
  premises.downVarTys = relArgTys ++
      map(\ p::(String, MaybeType) ->
            (p.1,
             case p.2 of
             | justType(t) -> t
             | nothingType() -> varType("__X" ++ toString(genInt()))
             end), boundVars.toList);
  premises.downSubst = emptySubst();
  unifyRelArgs.downSubst = premises.upSubst;
}

function buildExtIndThm
Metaterm ::= boundVars::Bindings rel::QName relArgs::[String]
             premises::[(Maybe<String>, Metaterm)] useExtSize::Boolean
{
  local args::[Term] =
      map(\ x::String -> nameTerm(toQName(x), nothingType()), relArgs);
  local n::String = freshName("N", boundVars.usedNames);
  local relPrem::Metaterm =
      relationMetaterm(rel,
         toTermList(args ++
            if useExtSize
            then [nameTerm(toQName(n), nothingType())]
            else []),
         emptyRestriction());
  local extSize::Metaterm =
      relationMetaterm(extSizeQName(rel.sub),
         toTermList(args ++
            if useExtSize
            then [nameTerm(toQName(n), nothingType())]
            else []),
         emptyRestriction());
  local acc::Metaterm =
      relationMetaterm(toQName("acc"),
         toTermList([nameTerm(toQName(n), nothingType())]),
         emptyRestriction());
  local conc::Metaterm =
      relationMetaterm(transRelQName(rel.sub), toTermList(args),
                       emptyRestriction());
  return
      bindingMetaterm(forallBinder(),
         if useExtSize
         then addBindings(n, nothingType(), boundVars)
         else boundVars,
         foldr(impliesMetaterm, conc,
               if useExtSize
               then extSize::acc::map(snd, premises)
               else relPrem::map(snd, premises)));
}


nonterminal ExtIndPremiseList with
   pps, abella_pp,
   toList<(Maybe<String>, Metaterm)>, len,
   typeEnv, constructorEnv, relationEnv,
   boundNames, usedNames,
   upSubst, downSubst, downVarTys, tyVars,
   toAbella<[(Maybe<String>, Metaterm)]>, toAbellaMsgs, proverState;
propagate typeEnv, constructorEnv, relationEnv, boundNames, downVarTys,
          tyVars, usedNames, proverState, toAbellaMsgs
   on ExtIndPremiseList;

abstract production emptyExtIndPremiseList
top::ExtIndPremiseList ::=
{
  top.pps = [];
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.upSubst = top.downSubst;

  top.toAbella = [];
}


abstract production addNameExtIndPremiseList
top::ExtIndPremiseList ::= name::String m::Metaterm
                           rest::ExtIndPremiseList
{
  top.pps = (text(name ++ " : ") ++ nest(3, m.pp))::rest.pps;
  top.abella_pp = name ++ " : " ++ m.abella_pp ++
                  if rest.abella_pp == "" then ""
                  else ", " ++ rest.abella_pp;

  top.toList = (just(name), m)::rest.toList;
  top.len = 1 + rest.len;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  top.toAbella = (just(name), m.toAbella)::rest.toAbella;
}


abstract production addExtIndPremiseList
top::ExtIndPremiseList ::= m::Metaterm rest::ExtIndPremiseList
{
  top.pps = (m.pp)::rest.pps;
  top.abella_pp = m.abella_pp ++ if rest.abella_pp == "" then ""
                                 else ", " ++ rest.abella_pp;

  top.toList = (nothing(), m)::rest.toList;
  top.len = 1 + rest.len;

  m.downSubst = top.downSubst;
  rest.downSubst = m.upSubst;
  top.upSubst = rest.upSubst;

  top.toAbella = (nothing(), m.toAbella)::rest.toAbella;
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
      | translationConstraintTheorem(q, x, b, _)::_ ->
        [errorMsg("Expected translation constraint obligation " ++
            justShow(q.pp))]
      | extensibleMutualTheoremGroup(thms, alsos, _)::_ ->
        [errorMsg("Expected theorem obligations " ++
            implode(", ", map(justShow, map((.pp), map(fst, thms)))) ++
            if null(alsos) then ""
            else " also " ++
                 implode(", ", map(justShow, map((.pp), map(fst, alsos)))))]
      | extSizeElement(rels, _)::_ ->
        [errorMsg("Expected Ext Size addition for " ++
            implode(", ", map(justShow, map((.pp), map(fst, rels)))))]
      | extIndElement(relInfo, _)::_ ->
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
      --split these out explicitly for better errors/catching if a
      --new constructor is added
      | nonextensibleTheorem(_, _, _)::_ ->
        error("Should be impossible (proveExtInd.toAbellaMsgs " ++
              "nonextensibleTheorem)")
      | splitElement(_, _)::_ ->
        error("Should be impossible (proveExtInd.toAbellaMsgs " ++
              "splitElement)")
      end;

  local obligations::[(QName, [String], Bindings, ExtIndPremiseList)] =
      case head(top.proverState.remainingObligations) of
      | extIndElement(r, _) -> r
      | _ -> error("Not possible (proveExtInd.obligations)")
      end;
  --This should only be accessed if there are no errors
  top.provingExtInds = obligations;
  top.provingTheorems =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList) ->
            --don't need the actual metaterm, only the name
            (extIndThmName(p.1), trueMetaterm()),
          obligations);

  --get the environment entry for the relation as well
  local fullRelInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                       RelationEnvItem)] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList) ->
            let rel::RelationEnvItem =
                decorate p.1 with {relationEnv=top.relationEnv;}.fullRel
            in
              (rel.name, p.2, p.3, p.4, rel)
            end,
          obligations);

  --whether or not to use ExtSize for the proof, or just the relation
  --because new ExtSize can only be declared for new relations, this
  --   matches what is done in other modules
  local useExtSize::Boolean =
      case rels of
      | [] -> true
      | q::rest ->
        case findExtSizeGroup(q, top.proverState) of
        | nothing() -> false
        | just(g) -> subset(rest, g)
        end
      end;
  body.useExtSize = useExtSize;

  --definition of R_T
  local transRelDef::TopCommand =
      buildTransRel(obligations, top.relationEnv);

  local body::ExtIndBody =
      foldr1(branchExtIndBody,
         map(\ here::(QName, [String], Bindings, ExtIndPremiseList) ->
               oneExtIndBody(here.3, here.1, here.2, here.4),
             obligations));
  body.startingGoalNum =
       if body.len > 1 then [1] else [];
  body.typeEnv = top.typeEnv;
  body.relationEnv = top.relationEnv;
  body.currentModule = top.currentModule;
  body.constructorEnv = top.constructorEnv;
  body.downDuringCommands = [];

  top.newTheorems = [];

  local extIndName::String = "$Ext_Ind_" ++ toString(genInt());
  top.toAbella =
      --relation definition
      [anyTopCommand(transRelDef)] ++
       --declare theorem
      [anyTopCommand(theoremDeclaration(toQName(extIndName), [],
                        body.toAbella))] ++
       --declare inductions:  acc (if using ExtSize) and rel
      (if useExtSize
       then [anyProofCommand(inductionTactic(noHint(), repeat(2, body.len)))]
       else []) ++
      [anyProofCommand(inductionTactic(noHint(), repeat(1, body.len)))] ++
       --split
      (if body.len > 1 then [anyProofCommand(splitTactic())]
                       else []) ++
       --initial set of during commands, which is at least intros
      map(anyProofCommand, head(body.duringCommands).2);

  top.duringCommands = tail(body.duringCommands);
}



abstract production extSizeDeclaration
top::TopCommand ::= rels::[(QName, [String])]
{
  top.pp = text("Ext_Size ") ++
           ppImplode(text(",") ++ line(),
              map(\ p::(QName, [String]) ->
                    nest(9, ppImplode(text(" "), p.1.pp::map(text, p.2))),
                  rels)) ++ text(".");
  top.abella_pp =
      "Ext_Size " ++
      implode(", ",
         map(\ p::(QName, [String]) ->
               implode(" ", p.1.abella_pp::p.2), rels)) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = extSizeLemmas;

  top.newExtSizeGroup =
      foldr(\ p::(Decorated QName with {relationEnv}, [String])
              rest::Maybe<[QName]> ->
              bind(rest, \ r::[QName] ->
                           if p.1.relFound then just(p.1.fullRel.name::r)
                                           else nothing()),
            just([]), decRels);

  production decRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), rels);

  top.toAbella =
      anyTopCommand(extSizeDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas);
  local extSizeDef::TopCommand =
      buildExtSize(map(\ q::Decorated QName with {relationEnv} ->
                         q.fullRel.name, map(fst, decRels)),
                       top.relationEnv);
  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                buildExtSizeLemmas(p.1.fullRel.name, p.2), decRels);

  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Ext Size for " ++
                          justShow(p.1.pp))]
                 else []) ++
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Ext Size " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                (if p.1.relFound &&  --len - 1 to drop prop
                    length(p.2) != p.1.fullRel.types.len - 1
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len - 1) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                p.1.relErrors ++
                if !p.1.relFound
                then []
                else (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     (if findExtSizeGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has ExtSize defined for it")]
                      else []), decRels);
}


abstract production addExtSize
top::TopCommand ::= oldRels::[QName] newRels::[(QName, [String])]
{
  top.pp = text("Add_Ext_Size ") ++
           ppImplode(text(",") ++ line(), map((.pp), oldRels)) ++
           (if null(newRels)
            then text("")
            else line() ++ text("with ") ++
                 ppImplode(text(",") ++ line(),
                    map(\ p::(QName, [String]) ->
                          nest(9, ppImplode(text(" "),
                                     p.1.pp::map(text, p.2))),
                        newRels))) ++ text(".");
  top.abella_pp =
      "Add_Ext_Size " ++
      implode(", ", map(justShow, map((.pp), oldRels))) ++
      (if null(newRels)
       then ""
       else " with " ++ implode(", ",
                           map(\ p::(QName, [String]) ->
                                 implode(" ", p.1.abella_pp::p.2),
                               newRels))) ++ ".";

  top.provingTheorems = [];
  top.duringCommands = [];
  top.afterCommands = [];
  top.keyRelModules = [];
  top.newTheorems = extSizeLemmas;

  top.newExtSizeGroup =
      bind(
         foldr(\ p::(Decorated QName with {relationEnv}, [String])
                 rest::Maybe<[QName]> ->
                 bind(rest, \ r::[QName] ->
                              if p.1.relFound then just(p.1.fullRel.name::r)
                                              else nothing()),
               just([]), decNewRels),
         \ r::[QName] -> just(oldRels ++ r));

  local decNewRels::[(Decorated QName with {relationEnv}, [String])] =
      map(\ p::(QName, [String]) ->
            (decorate p.1 with {
               relationEnv = top.relationEnv;
             }, p.2), newRels);

  top.toAbella =
      anyTopCommand(extSizeDef)::
      flatMap(\ p::(QName, Metaterm) ->
                [anyTopCommand(theoremDeclaration(p.1, [], p.2)),
                 anyProofCommand(skipTactic())],
              extSizeLemmas);
  local extSizeDef::TopCommand =
      buildExtSize(map(fst, obligations) ++
                   map(\ q::Decorated QName with {relationEnv} ->
                         q.fullRel.name, map(fst, decNewRels)),
                   top.relationEnv);
  local extSizeLemmas::[(QName, Metaterm)] =
      flatMap(\ p::(QName, [String]) ->
                buildExtSizeLemmas(p.1, p.2), obligations ++ newRels);

  local obligations::[(QName, [String])] =
      case head(top.proverState.remainingObligations) of
      | extSizeElement(r, _) -> r
      | _ -> error("Not possible (addExtSize.obligations)")
      end;

  top.toAbellaMsgs <-
      case top.proverState.remainingObligations of
      | [] -> [errorMsg("No obligations left to prove")]
      | translationConstraintTheorem(q, x, b, _)::_ ->
        [errorMsg("Expected translation constraint obligation" ++
            justShow(q.pp))]
      | extensibleMutualTheoremGroup(thms, alsos, _)::_ ->
        [errorMsg("Expected theorem obligations " ++
            implode(", ", map(justShow, map((.pp), map(fst, thms)))) ++
            if null(alsos) then ""
            else " also " ++
                 implode(", ", map(justShow, map((.pp), map(fst, alsos)))))]
      | extIndElement(relInfo, _)::_ ->
        [errorMsg("Expected Ext Ind for " ++
            implode(", ", map(justShow, map((.pp), map(fst, relInfo)))))]
      | extSizeElement(relInfo, _)::_ ->
        let expectedNames::[QName] = map(fst, relInfo)
        in
          if setEq(oldRels, expectedNames)
          then []
          else if subset(oldRels, expectedNames)
          then let missing::[QName] = removeAll(oldRels, expectedNames)
               in
                 [errorMsg("Missing relation" ++
                     (if length(missing) == 1 then " " else "s ") ++
                     implode(", ", map(justShow,
                        map((.pp), removeAll(oldRels, expectedNames)))))]
               end
          else if subset(expectedNames, oldRels)
          then [errorMsg("Too many relations; should not have " ++
                   implode(", ", map(justShow,
                      map((.pp), removeAll(expectedNames, oldRels)))))]
          else [errorMsg("Expected ExtSize addition" ++
                   (if length(expectedNames) == 1 then "" else "s") ++
                   " " ++ implode(", ",
                             map(justShow, map((.pp), expectedNames))))]
        end
      --split these out explicitly for better errors/catching if a
      --new constructor is added
      | nonextensibleTheorem(_, _, _)::_ ->
        error("Should be impossible (addExtSize.toAbellaMsgs " ++
              "nonextensibleTheorem)")
      | splitElement(_, _)::_ ->
        error("Should be impossible (addExtSize.toAbellaMsgs " ++
              "splitElement)")
      end;
  top.toAbellaMsgs <-
      flatMap(\ p::(Decorated QName with {relationEnv}, [String]) ->
                (if length(nub(p.2)) != length(p.2)
                 then [errorMsg("Repeated arguments in Ext Size for " ++
                          justShow(p.1.pp))]
                 else []) ++
                flatMap(\ x::String ->
                          if !isCapitalized(x)
                          then [errorMsg("Arguments in Ext Size " ++
                                   "declaration must be capitalized, but " ++
                                   x ++ " is not")]
                          else [], nub(p.2)) ++
                (if p.1.relFound && length(p.2) != p.1.fullRel.types.len
                 then [errorMsg("Expected " ++
                          toString(p.1.fullRel.types.len) ++
                          " arguments to " ++ justShow(p.1.pp) ++
                          " but found " ++ toString(length(p.2)))]
                 else []) ++
                p.1.relErrors ++
                if !p.1.relFound
                then []
                else (if !sameModule(top.currentModule, p.1.fullRel.name)
                      then [errorMsg("Relation " ++
                               justShow(p.1.fullRel.name.pp) ++
                               " is not from this module")]
                      else []) ++
                     (if findExtSizeGroup(p.1.fullRel.name,
                            top.proverState).isJust
                      then [errorMsg("Relation " ++
                              justShow(p.1.fullRel.name.pp) ++
                              " already has ExtSize defined for it")]
                      else []), decNewRels);
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
                bindingMetaterm(existsBinder(), toBindings(x.1), x.2))
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
TopCommand ::= relInfo::[(QName, [String], Bindings, ExtIndPremiseList)]
               relEnv::Env<RelationEnvItem>
{
  local fullRelInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                       RelationEnvItem)] =
      map(\ p::(QName, [String], Bindings, ExtIndPremiseList) ->
            let rel::RelationEnvItem =
                decorate p.1 with {relationEnv=relEnv;}.fullRel
            in
              (rel.name, p.2, p.3, p.4, rel)
            end,
          relInfo);
  local defInfo::[(QName, ([String], [String], Maybe<Metaterm>),
                   [([Term], Maybe<Metaterm>)], RelationEnvItem)] =
      buildTransRelDefInfo(fullRelInfo);
  return buildTransRelDef(defInfo);
}

--Gather up the information we need to build the R_T def clauses
function buildTransRelDefInfo
[(QName, ([String], [String], Maybe<Metaterm>),
  [([Term], Maybe<Metaterm>)], RelationEnvItem)] ::=
          relInfo::[(QName, [String], Bindings, ExtIndPremiseList,
                     RelationEnvItem)]
{
  local r::(QName, [String], Bindings, ExtIndPremiseList,
            RelationEnvItem) = head(relInfo);
  local pcIndex::Integer = r.5.pcIndex;
  --split out clauses for non-unknownK and unknownK for this relation,
  --   of which there is <= 1
  local split::([([Term], Maybe<Metaterm>)], [([Term], Maybe<Metaterm>)]) =
      partition(\ p::([Term], Maybe<Metaterm>) ->
                  let pc::Term = elemAtIndex(p.1, pcIndex)
                  in
                    !pc.isUnknownTermK ||
                    !decorate pc with {
                        relationEnv = buildEnv([r.5]);
                        typeEnv = error("not actually needed");
                     }.unknownId.isJust
                  end,
                r.5.defsList);
  local defList::[([Term], Maybe<Metaterm>)] = split.1;
  --(args to conclusion, existentially-bound vars for body, binderless body)
  local qRule::([String], [String], Maybe<Metaterm>) =
      if null(split.2)
      then ([], [], nothing())
      else let kClause::([Term], Maybe<Metaterm>) = head(split.2)
           in
           let usedNames::[String] =
               case kClause.2 of
               | nothing() -> []
               | just(m) -> m.usedNames
               end ++
               flatMap((.usedNames), kClause.1)
           in
           let kName::String = freshName("K", usedNames)
           in
           let newArgs::[String] =
               map(\ t::Term ->
                     case t of
                     | nameTerm(v, _) -> v.shortName
                     | unknownKTerm(_) -> kName
                     | _ -> error("Nothing else should be here")
                     end, kClause.1)
           in
           let newBodyPieces::([String], Maybe<Metaterm>) =
               case kClause.2 of
               | nothing() -> ([], nothing())
               | just(bindingMetaterm(existsBinder(), binds, body)) ->
                 (map(fst, binds.toList), dropFalsePrem(body))
               | just(m) -> ([], dropFalsePrem(m))
               end
           in
             (newArgs, newBodyPieces)
           end end end end end;
  local firstRel::(QName, ([String], [String], Maybe<Metaterm>),
                   [([Term], Maybe<Metaterm>)], RelationEnvItem) =
      (r.1, qRule, defList, r.5);
  return case relInfo of
         | [] -> []
         | _::t -> firstRel::buildTransRelDefInfo(t)
         end;
}

{-
  Build all the definitional clauses for the translation version of
  the relations in rels and turn them into a definition
-}
function buildTransRelDef
TopCommand ::=
--[(rel, Q rule: (args to conclusion, existentially-bound vars for body,
--                binderless body), def clauses: (args, body), env item)]
   rels::[(QName, ([String], [String], Maybe<Metaterm>),
           [([Term], Maybe<Metaterm>)], RelationEnvItem)]
{
  local preds::[(QName, Type)] =
      map(\ p::(QName, ([String], [String], Maybe<Metaterm>),
                [([Term], Maybe<Metaterm>)], RelationEnvItem) ->
            (transRelQName(p.1.sub),
             foldr1(arrowType, p.4.types.toList)),
          rels);
  local allRels::[QName] = map(fst, rels);
  local fullReplaceRels::(Maybe<Metaterm> ::= Maybe<Metaterm>) =
      \ m::Maybe<Metaterm> ->
        bind(m, \ m::Metaterm ->
                  case m of
                  | bindingMetaterm(existsBinder(), b, m) ->
                    just(bindingMetaterm(existsBinder(), b,
                            replaceRelsTransRels(allRels, m)))
                  | _ -> just(replaceRelsTransRels(allRels, m))
                  end);
  local defs::[Def] =
      flatMap(\ p::(QName, ([String], [String], Maybe<Metaterm>),
                    [([Term], Maybe<Metaterm>)], RelationEnvItem) ->
                let transRelledQBody::Maybe<Metaterm> =
                    fullReplaceRels(p.2.3)
                in
                let transRelledDefs::[([Term], Maybe<Metaterm>)] =
                    map(\ p::([Term], Maybe<Metaterm>) ->
                          (p.1, fullReplaceRels(p.2)), p.3)
                in
                  buildTransRelClauses(p.1, transRelledDefs,
                     p.2.1, p.2.2, transRelledQBody,
                     p.4.pcIndex, allRels)
                end end,
              rels);
  return definitionDeclaration(preds,
            if null(defs) --check to find error loc in debugging
            then error("buildTransRelDef null list")
            else foldrLastElem(consDefs, singleDefs, defs));
}

{-
  Build the clauses for the translation version of a single relation
  as part of a group of relations (allRels)
-}
function buildTransRelClauses
[Def] ::= rel::QName defs::[([Term], Maybe<Metaterm>)]
          qRuleArgs::[String] qRuleBindings::[String]
          qRuleBody::Maybe<Metaterm>
          --relArgs::[String] transArgs::[Term] transTy::QName
          --original::String translated::String
          pcIndex::Integer allRels::[QName]
{
  local transRel::QName = transRelQName(rel.sub);
  local usedVars::[String] =
      case head(defs) of
      | (tms, just(m)) -> m.usedNames ++ flatMap((.usedNames), tms)
      | (tms, nothing()) -> flatMap((.usedNames), tms)
      end;

  --fresh names for bound variables in body of Q rule
  --disjoint from the names in head(defs) and qRuleArgs
  local freshQBindings::[String] =
      foldr(\ x::String thusFar::[String] ->
              freshName(x, thusFar ++ qRuleArgs ++ usedVars)::thusFar,
            [], qRuleBindings);
  local freshQBody::Maybe<Metaterm> =
      case qRuleBody of
      | just(m) ->
        just(
           head(safeReplace([m], qRuleBindings,
                   map(\ x::String -> nameTerm(toQName(x), nothingType()),
                       freshQBindings))))
      | nothing() -> nothing()
      end;

  local pc::Term = elemAtIndex(head(defs).1, pcIndex);

  --replace vars from Q rule conclusion with terms from rule and
  --unknownK with pc
  local replacedQBody::Maybe<Metaterm> =
      case freshQBody of
      | just(m) ->
        just(decorate head(safeReplace([m], qRuleArgs,
                                       head(defs).1)) with {
                replaceUnknownK = pc;
             }.unknownKReplaced)
      | nothing() -> nothing()
      end;

  --determine whether this is a rule needing a translation
  local isExtRule::Boolean =
      let constr::QName = pc.headConstructor
      in --rules for K's getting here are instantiated default rules,
         --  which are host rules
        !pc.isUnknownTermK && !sameModule(rel.moduleName, constr)
      end;

  --new body for the rule, with all bindings
  local modBody::Maybe<Metaterm> =
     case head(defs).2, replacedQBody of
     | mm, _ when !isExtRule -> mm
     | just(bindingMetaterm(existsBinder(), binds, body)), just(m2) ->
       just(bindingMetaterm(existsBinder(),
               foldr(addBindings(_, nothingType(), _), binds,
                     freshQBindings),
               andMetaterm(body, m2)))
     | just(m1), just(m2) ->
       if null(freshQBindings)
       then just(andMetaterm(m1, m2))
       else just(bindingMetaterm(existsBinder(),
                    toBindings(freshQBindings),
                    andMetaterm(m1, m2)))
     | just(m), nothing() -> just(m)
     | nothing(), just(m) ->
       if null(freshQBindings)
       then just(m)
       else just(bindingMetaterm(existsBinder(),
                    toBindings(freshQBindings), m))
     | nothing(), nothing() -> nothing()
     end;

  local hereDef::Def =
      case modBody of
      | just(body) -> ruleDef(transRel, toTermList(head(defs).1), body)
      | nothing() -> factDef(transRel, toTermList(head(defs).1))
      end;

  return case defs of
         | [] -> []
         | _::tl -> hereDef::buildTransRelClauses(rel, tl, qRuleArgs,
                                qRuleBindings, qRuleBody, pcIndex, allRels)
         end;
}

{-
  Replace all occurrences of relations in rels in the given metaterm with
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
  Q rules have bodies of the form
     exists x, m_1 /\ ... /\ m_n /\ (0 = 0 -> false)
  This assumes the binder has been lifted from the beginning and then
  removes the (0 = 0 -> false) assumption.
-}
function dropFalsePrem
Maybe<Metaterm> ::= m::Metaterm
{
  return case m.splitConjunctions of
         | x::y::r -> just(foldr1(andMetaterm, init(x::y::r)))
         | _ -> nothing() --[_] or []
         end;
}





{--------------------------------------------------------------------
  Extension Size Lemmas
 --------------------------------------------------------------------}
{-
  Build the lemmas for using the extension size:
  1. Size is always non-negative
  2. Size is always an integer (is_integer)
  3. ExtSize version implies the relation itself
  4. Relation itself implies the ExtSize version
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
  local nonNegThmName::QName = ext_ind_pos_name(rel);
  local nonNegThmBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(toQName(integerLessEqName),
               toTermList([integerToIntegerTerm(0),
                           basicNameTerm(numName)]),
               emptyRestriction())));

  --is int:  forall \bar{x} n.  extSize \bar{x} n  ->  is_integer n
  local isIntThmName::QName = ext_ind_is_int_name(rel);
  local isIntThmBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(toQName("is_integer"),
               toTermList([basicNameTerm(numName)]),
               emptyRestriction())));

  --drop:  forall \bar{x} n.  extSize \bar{x} n  ->  R \bar{x}
  local dropExtSizeName::QName = drop_ext_ind_name(rel);
  local dropExtSizeBody::Metaterm =
      bindingMetaterm(forallBinder(), binds,
         impliesMetaterm(extSize,
            relationMetaterm(rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction())));

  --add:  forall \bar{x}.  R \bar{x}  ->  exists n.  extSize \bar{x} n
  local addExtSizeName::QName = add_ext_ind_name(rel);
  local addExtSizeBody::Metaterm =
      bindingMetaterm(forallBinder(), toBindings(argNames),
         impliesMetaterm(
            relationMetaterm(rel,
               toTermList(map(basicNameTerm, argNames)),
               emptyRestriction()),
            bindingMetaterm(existsBinder(), toBindings([numName]),
               extSize)));

  return [(nonNegThmName, nonNegThmBody),
          (isIntThmName, isIntThmBody),
          (dropExtSizeName, dropExtSizeBody),
          (addExtSizeName, addExtSizeBody)];
}


function ext_ind_pos_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "ext_ind_pos_" ++ rel.shortName);
}
function ext_ind_is_int_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "ext_ind_is_int_" ++ rel.shortName);
}
function drop_ext_ind_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "drop_ext_ind_" ++ rel.shortName);
}
function add_ext_ind_name
QName ::= rel::QName
{
  return
      addQNameBase(rel.moduleName, "add_ext_ind_" ++ rel.shortName);
}
