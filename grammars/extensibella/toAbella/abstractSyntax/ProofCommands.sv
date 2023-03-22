grammar extensibella:toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   --pp/abella_pp should end with two spaces
   pp, abella_pp,
   boundNames,
   currentModule, typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<[ProofCommand]>, toAbellaMsgs,
   isUndo,
   stateListIn, stateListOut;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, boundNames, toAbellaMsgs on ProofCommand;

aspect default production
top::ProofCommand ::=
{
  top.isUndo = false;
  top.stateListOut =
      error("Should only access ProofCommand.stateListOut for undo");
}


abstract production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.pp = h.pp ++ "induction on " ++
           implode(" ", map(toString, nl)) ++ ".  ";
  top.abella_pp = h.pp ++ "induction on " ++
                  implode(" ", map(toString, nl)) ++ ".  ";

  top.toAbella = [top];

  --Check none of the numbers correspond to extensible relations
  --Only way for induction on those should be extensible theorems
  --If that is not the case, I can change this
  local goal::Metaterm = top.proverState.state.goal.fromJust;
  local splits::[[Metaterm]] =
      map((.splitImplies), goal.splitConjunctions);
  top.toAbellaMsgs <-
      if !top.proverState.state.inProof
      then [] --not a proof
      else if length(nl) != length(splits)
      then [errorMsg("Expected " ++ toString(length(splits)) ++
               " induction arguments but was given " ++
               toString(length(nl)))]
      else
        flatMap( --(induction integer, premises and goal)
           \ p::(Integer, [Metaterm]) ->
             if p.1 >= length(p.2)
             then [errorMsg("Premise " ++ toString(p.1) ++ " does " ++
                            "not exist")]
             else 
               case elemAtIndex(p.2, p.1 - 1) of
               | relationMetaterm(rel, args, r) --allow induction on append
                 when rel.shortName == appendName -> []
               | relationMetaterm(rel, args, r) ->
                 let decRel::Decorated QName with {relationEnv} =
                     decorate rel with {
                       relationEnv = top.relationEnv;}
                 in
                   if !decRel.fullRel.isExtensible
                   then []
                   else [errorMsg("Cannot induct on extensible " ++
                            "judgment " ++ elemAtIndex(p.2, p.1 - 1).pp ++
                            " outside of extensible theorems")]
                 end
               | _ -> [errorMsg("Cannot induct on non-relation")]
               end,
           zipWith(pair, nl, splits));
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = h.pp ++ "coinduction.  ";
  top.abella_pp = h.pp ++ "coinduction.  ";

  top.toAbella = [top];
}


abstract production introsTactic
top::ProofCommand ::= names::[String]
{
  local namesString::String =
     if null(names)
     then ""
     else " " ++ implode(" ", names);
  top.pp = "intros" ++ namesString ++ ".  ";
  top.abella_pp = "intros" ++ namesString ++ ".  ";

  top.toAbella = [top];
}


abstract production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::ApplyArgs withs::Withs
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local argsString::String =
     if args.len == 0
     then ""
     else " to " ++ args.pp;
  local withsString::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.pp;
  top.pp = h.pp ++ "apply " ++ depthString ++ theorem.pp ++
           argsString ++ withsString ++ ".  ";
  local argsString_abella::String =
     if args.len == 0
     then ""
     else " to " ++ args.abella_pp;
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp =
      h.pp ++ "apply " ++ depthString ++ theorem.abella_pp ++
      argsString_abella ++ withsString_abella ++ ".  ";

  top.toAbella =
      [applyTactic(h, depth, theorem.toAbella,
                   args.toAbella, withs.toAbella)];
}


abstract production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable
                      withs::Withs
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local withsString::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.pp;
  top.pp = "backchain " ++ depthString ++ theorem.pp ++
           withsString ++ ".  ";
  local withsString_abella::String =
     if withs.len == 0
     then ""
     else " with " ++ withs.abella_pp;
  top.abella_pp = "backchain " ++ depthString ++ theorem.abella_pp ++
                  withsString_abella ++ ".  ";

  top.toAbella =
      [backchainTactic(depth, theorem.toAbella, withs.toAbella)];
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then " (keep).  "
                                             else ".  ";
  top.abella_pp = h.pp ++ "case " ++ hyp ++ if keep then " (keep).  "
                                                    else ".  ";

  top.toAbella = [top];

  local maybeHypBody::Maybe<Metaterm> =
      lookup(hyp, top.proverState.state.hypList);
  local hypBody::Metaterm = maybeHypBody.fromJust;
  hypBody.relationEnv = top.relationEnv;
  hypBody.constructorEnv = top.constructorEnv;
  --check hyp isn't an extensible relation or has PC filled in
  top.toAbellaMsgs <-
      if !maybeHypBody.isJust
      then [errorMsg("Unknown hypothesis " ++ hyp)]
      else
         case hypBody of
         | relationMetaterm(rel, args, r) ->
           if !rel.relFound
           then [] --already covered
           else if rel.fullRel.name == is_string
           then [errorMsg("Cannot do case analysis on " ++
                    is_string.pp ++ " relation")] --because $is_char
           else if !rel.fullRel.isExtensible
           then [] --can do case analysis on non-extensible whenever
           else if length(args.isStructuredList) <= rel.fullRel.pcIndex
           then [] --too few args
           else if elemAtIndex(args.isStructuredList,
                               rel.fullRel.pcIndex)
           then [] --pc is structured
           else [errorMsg("Cannot do case analysis on extensible " ++
                    "relation " ++ rel.pp ++ " with unstructured " ++
                    "primary component")]
         | _ -> []
         end;
}


abstract production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  top.pp = h.pp ++ "assert " ++ depthString ++ m.pp ++ ".  ";
  top.abella_pp = h.pp ++ "assert " ++ depthString ++
                  m.abella_pp ++ ".  ";

  top.toAbella = [assertTactic(h, depth, m.toAbella)];
}


abstract production existsTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.pp = "exists " ++ ew.pp ++ ".  ";
  top.abella_pp = "exists " ++ ew.abella_pp ++ ".  ";

  top.toAbella = [existsTactic(ew.toAbella)];
}


abstract production witnessTactic
top::ProofCommand ::= ew::EWitnesses
{
  top.pp = "witness " ++ ew.pp ++ ".  ";
  top.abella_pp = "witness " ++ ew.abella_pp ++ ".  ";

  top.toAbella = [witnessTactic(ew.toAbella)];
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = "search.  ";
  top.abella_pp = "search.  ";

  top.toAbella = [top];
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = "search " ++ toString(n) ++ ".  ";
  top.abella_pp = "search " ++ toString(n) ++ ".  ";

  top.toAbella = [top];
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = "search with " ++ sw.pp ++ ".  ";
  top.abella_pp = "search with " ++ sw.abella_pp ++ ".  ";

  top.toAbella = [searchWitnessTactic(sw.toAbella)];
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = "async.  ";
  top.abella_pp = "async.  ";

  top.toAbella = [top];
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = "split.  ";
  top.abella_pp = "split.  ";

  top.toAbella = [top];
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = "split*.  ";
  top.abella_pp = "split*.  ";

  top.toAbella = [top];
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = "left.  ";
  top.abella_pp = "left.  ";

  top.toAbella = [top];
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = "right.  ";
  top.abella_pp = "right.  ";

  top.toAbella = [top];
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = "skip.  ";
  top.abella_pp = "skip.  ";

  top.toAbella = [top];
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = "abort.  ";
  top.abella_pp = "abort.  ";

  top.toAbella = [top];
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = "undo.  ";
  top.abella_pp = "undo.  ";

  top.toAbella = repeat(undoCommand(), head(top.stateListIn).1);

  top.isUndo = true;
  top.stateListOut = tail(top.stateListIn);
}


--I have no idea what the arrow does, but there are clears with and without it
abstract production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.pp = "clear " ++ (if hasArrow then "-> " else "") ++
           implode(" ", removes) ++ ".  ";
  top.abella_pp = top.pp;

  top.toAbella = [top];
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";
  top.abella_pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  top.toAbella = [top];
}


--this assumes newText does NOT include the quotation marks
abstract production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  top.pp = "abbrev " ++ implode(" ", hyps) ++
           " \"" ++ newText ++ "\".  ";
  top.abella_pp = top.pp;

  top.toAbella = error("Cannot abbreviate");
  top.toAbellaMsgs <-
     [errorMsg("Abbreviation of hypotheses not currently supported")];
}


abstract production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  top.pp = "unabbrev " ++ implode(" ", hyps) ++ "\".  ";
  top.abella_pp = top.pp;

  top.toAbella = error("Cannot abbreviate");
  top.toAbellaMsgs <-
     [errorMsg("Abbreviation of hypotheses not currently supported")];
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = "permute " ++ foldr1(\a::String b::String -> a ++ " " ++ b, names) ++
           hypString ++ ".  ";
  top.abella_pp = top.pp;

  top.toAbella = [top];
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  "
                                                  else ".  ";
  top.abella_pp = top.pp;

  top.toAbella = [top];
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.pp = "unfold " ++ id.pp ++ if all then "(all).  " else ".  ";
  top.abella_pp = "unfold " ++ id.abella_pp ++ if all then "(all).  "
                                                      else ".  ";

  top.toAbella = [unfoldIdentifierTactic(id.fullRel.name, all)];

  top.toAbellaMsgs <- id.relErrors;
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";
  top.abella_pp = top.pp;

  top.toAbella = [top];
}





nonterminal Clearable with
   pp, abella_pp,
   toAbella<Clearable>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate toAbellaMsgs, proverState,
          typeEnv, constructorEnv, relationEnv on Clearable;

--I don't know what the star is, but some have it
abstract production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  local instString::String =
     if instantiation.pp == ""
     then ""
     else "[" ++ instantiation.pp ++ "]";
  top.pp = (if star then "*" else "") ++ hyp.pp ++ instString;
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = (if star then "*" else "") ++ hyp.abella_pp ++
                  instString_abella;

  production hypFound::Boolean =
     foldr(\ p::(String, Metaterm) found::Boolean ->
             found || p.1 == hyp.shortName,
           false, top.proverState.state.hypList);
  production possibleThms::[(QName, Metaterm)] =
     findTheorem(hyp, top.proverState);
  top.toAbella =
      clearable(star,
                if hyp.isQualified || hypFound
                then hyp
                else head(possibleThms).1, instantiation.toAbella);

  top.toAbellaMsgs <-
      if hypFound
      then []
      else case possibleThms of
           | [] -> [errorMsg("Unknown hypothesis or theorem " ++
                             hyp.pp)]
           | [_] -> []
           | l -> [errorMsg("Indeterminate theorem " ++ hyp.pp ++
                            "; possibilities are " ++
                            implode(", ", map((.pp), map(fst, l))))]
           end;
}





nonterminal ApplyArgs with
   pp, abella_pp,
   toList<ApplyArg>, len,
   boundNames,
   toAbella<ApplyArgs>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on ApplyArgs;

abstract production endApplyArgs
top::ApplyArgs ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.toAbella = endApplyArgs();
}


abstract production addApplyArgs
top::ApplyArgs ::= a::ApplyArg rest::ApplyArgs
{
  top.pp = a.pp ++ if rest.pp == "" then "" else " " ++ rest.pp;
  top.abella_pp = a.abella_pp ++
           if rest.abella_pp == "" then "" else " " ++ rest.abella_pp;

  top.toList = a::rest.toList;
  top.len = 1 + rest.len;

  top.toAbella = addApplyArgs(a.toAbella, rest.toAbella);
}






nonterminal ApplyArg with
   pp, abella_pp,
   boundNames,
   toAbella<ApplyArg>, toAbellaMsgs,
   typeEnv, constructorEnv, relationEnv, proverState;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on ApplyArg;

abstract production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  local instString::String =
     if instantiation.pp == ""
     then ""
     else "[" ++ instantiation.pp ++ "]";
  top.pp = hyp ++ instString;
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = hyp ++ instString;

  top.toAbella = hypApplyArg(hyp, instantiation.toAbella);
}

abstract production starApplyArg
top::ApplyArg ::= name::String instantiation::TypeList
{
  local instString::String =
     if instantiation.pp == ""
     then ""
     else "[" ++ instantiation.pp ++ "]";
  top.pp = "*" ++ name ++ instString;
  local instString_abella::String =
     if instantiation.abella_pp == ""
     then ""
     else "[" ++ instantiation.abella_pp ++ "]";
  top.abella_pp = "*" ++ name ++ instString_abella;

  top.toAbella = starApplyArg(name, instantiation.toAbella);
}





nonterminal Withs with
   pp, abella_pp,
   toList<(String, Term)>, len,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState,
   toAbella<Withs>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs, boundNames on Withs;

abstract production endWiths
top::Withs ::=
{
  top.pp = "";
  top.abella_pp = "";

  top.toList = [];
  top.len = 0;

  top.toAbella = endWiths();
}


abstract production addWiths
top::Withs ::= name::String term::Term rest::Withs
{
  top.pp = name ++ " = " ++ term.pp ++
           if rest.len == 0 then "" else ", " ++ rest.pp;
  top.abella_pp = name ++ " = " ++ term.abella_pp ++
                 if rest.len == 0 then "" else ", " ++ rest.abella_pp;

  top.toList = (name, term)::rest.toList;
  top.len = 1 + rest.len;

  top.toAbella = addWiths(name, term.toAbella, rest.toAbella);
}





nonterminal EWitnesses with
   pp, abella_pp,
   boundNames,
   typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<EWitnesses>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on EWitnesses;

abstract production oneEWitnesses
top::EWitnesses ::= e::EWitness
{
  top.pp = e.pp;
  top.abella_pp = e.abella_pp;

  top.toAbella = oneEWitnesses(e.toAbella);
}


abstract production addEWitnesses
top::EWitnesses ::= e::EWitness rest::EWitnesses
{
  top.pp = e.pp ++ ", " ++ rest.pp;
  top.abella_pp = e.abella_pp ++ ", " ++ rest.abella_pp;

  top.toAbella = addEWitnesses(e.toAbella, rest.toAbella);
}





nonterminal EWitness with
   pp, abella_pp,
   boundNames,
   typeEnv, constructorEnv, relationEnv, proverState,
   toAbella<EWitness>, toAbellaMsgs;
propagate typeEnv, constructorEnv, relationEnv,
          proverState, boundNames, toAbellaMsgs on EWitness;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;
  top.abella_pp = t.abella_pp;

  top.toAbella = termEWitness(t.toAbella);
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = name ++ " = " ++ t.pp;
  top.abella_pp = name ++ " = " ++ t.abella_pp;

  top.toAbella = nameEWitness(name, t.toAbella);
}





nonterminal HHint with
   pp;

abstract production nameHint
top::HHint ::= name::String
{
  top.pp = name ++ ": ";
}


abstract production noHint
top::HHint ::=
{
  top.pp = "";
}

