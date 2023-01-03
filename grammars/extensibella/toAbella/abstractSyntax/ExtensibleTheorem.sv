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
}


abstract production proveObligations
top::TopCommand ::= names::[QName]
{
  top.pp = "Prove " ++ implode(", ", map((.pp), names)) ++ ".\n";
  top.abella_pp =
      error("proveObligations.abella_pp should not be accessed");

  top.toAbella = error("proveObligations.toAbella");
  --Need to check these are the right things to prove

  top.provingTheorems = error("proveObligations.provingTheorems");

  top.duringCommands = error("proveObligations.duringCommands");

  top.afterCommands = error("proveObligations.afterCommands");
}





nonterminal ExtThms with
   pp, len,
   toAbella<Metaterm>, toAbellaMsgs,
   provingTheorems,
   inductionNums,
   startingGoalNum, duringCommands,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs on ExtThms;

--prefix for the subgoals arising from a theorem
inherited attribute startingGoalNum::SubgoalNum;
--gather indices for induction
synthesized attribute inductionNums::[Integer];

abstract production endExtThms
top::ExtThms ::=
{
  top.pp = "";

  top.len = 0;

  top.toAbella = trueMetaterm();

  top.provingTheorems = [];

  top.inductionNums = [];

  top.duringCommands = [];
}


abstract production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String rest::ExtThms
{
  top.pp = name.pp ++ " : forall " ++ bindings.pp ++ ", " ++
           body.pp ++ " on " ++ onLabel ++
           if rest.pp == "" then "" else " /\\ " ++ rest.pp;

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
        foldr(\ p::(Maybe<String>, Decorated Metaterm) rest::[String] ->
                case p.1 of
                | just(x) -> x::rest
                | nothing() ->
                  makeUniqueNameFromBase("H", rest ++ labels)::rest
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

  top.toAbellaMsgs <-
      case lookupBy(\ a::Maybe<String> b::Maybe<String> ->
                      a.isJust && b.isJust && a.fromJust == b.fromJust,
                    just(onLabel), body.premises) of
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
           else [errorMsg("Declared predicate name " ++ name.pp ++
                    " does not have correct module (expected " ++
                    top.currentModule.pp ++ ")")]
      else [];

  top.provingTheorems = (fullName, body.thm)::rest.provingTheorems;

  rest.startingGoalNum = [head(top.startingGoalNum) + 1];

  top.duringCommands =
      --intros and case immediately
      [(top.startingGoalNum,
        [introsTactic(introsNames),
         caseTactic(nameHint(onLabel), onLabel, true)])];
}





nonterminal ExtBody with
   pp,
   toAbella<Metaterm>, toAbellaMsgs,
   premises, thm,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          currentModule, proverState, toAbellaMsgs on ExtBody;

--Decorated metaterm so we have the information from the envs
synthesized attribute premises::[(Maybe<String>, Decorated Metaterm)];
--Metaterm underlying the body
synthesized attribute thm::Metaterm;

abstract production endExtBody
top::ExtBody ::= conc::Metaterm
{
  top.pp = conc.pp;

  top.thm = conc;

  top.toAbella = conc.toAbella;

  conc.boundNames = top.boundNames;

  top.premises = [];
}


abstract production addLabelExtBody
top::ExtBody ::= label::String m::Metaterm rest::ExtBody
{
  top.pp = label ++ " : (" ++ m.pp ++ ") -> " ++ rest.pp;

  top.thm = impliesMetaterm(m, rest.thm);

  top.toAbella = impliesMetaterm(m.toAbella, rest.toAbella);

  m.boundNames = top.boundNames;
  rest.boundNames = top.boundNames;

  top.premises = (just(label), m)::rest.premises;
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

  top.premises = (nothing(), m)::rest.premises;
}
