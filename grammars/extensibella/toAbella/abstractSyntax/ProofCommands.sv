grammar extensibella:toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   --pp should end with two spaces
   pp,
   languageCtx, proverState,
   toAbella<[ProofCommand]>, toAbellaMsgs;
propagate languageCtx, proverState on ProofCommand;


abstract production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  top.pp = h.pp ++ "induction on " ++ implode(" ", map(toString, nl)) ++ ".  ";

  top.toAbella = [top];

  --Need to check none of the numbers correspond to extensible relations
  --Only way for induction on those should be extensible theorems, I think
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = h.pp ++ "coinduction.  ";

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

  top.toAbella = [top];
}


abstract production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::[ApplyArg] withs::[(String, Term)]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local argsString::String =
     if null(args)
     then ""
     else " to " ++ implode(" ", map((.pp), args));
  local withsString::String =
     if null(withs)
     then ""
     else " with " ++
          implode(", ", map(\ p::(String, Term) ->
                              p.1 ++ " = " ++ p.2.pp, withs));
  top.pp = h.pp ++ "apply " ++ depthString ++ theorem.pp ++
           argsString ++ withsString ++ ".  ";

  local transArgs::[ApplyArg] =
        map(\ a::ApplyArg -> decorate a with {
                                languageCtx = top.languageCtx;
                             }.toAbella, args);
  local transWiths::[(String, Term)] =
        map(\ p::(String, Term) ->
              (p.1, decorate p.2 with {
                       languageCtx = top.languageCtx;
                    }.toAbella), withs);
  top.toAbella =
      [applyTactic(h, depth, theorem.toAbella, transArgs, transWiths)];
}


abstract production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable
                      withs::[Pair<String Term>]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local withsString::String =
     if null(withs)
     then ""
     else " with " ++
          implode(", ", map(\ p::(String, Term) ->
                              p.1 ++ " = " ++ p.2.pp, withs));
  top.pp = "backchain " ++ depthString ++ theorem.pp ++
           withsString ++ ".  ";

  local transWiths::[(String, Term)] =
        map(\ p::(String, Term) ->
              (p.1, decorate p.2 with {
                       languageCtx = top.languageCtx;
                    }.toAbella), withs);
  top.toAbella =
      [backchainTactic(depth, theorem.toAbella, transWiths)];
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then " (keep).  " else ".  ";

  top.toAbella = [top];

  --need to check hyp isn't an extensible relation or
  --it has its PC filled in
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

  top.toAbella = [assertTactic(h, depth, m.toAbella)];
}


abstract production existsTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in existsTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "exists " ++ buildWitnesses(ew) ++ ".  ";

  top.toAbella = [existsTactic(map((.toAbella), ew))];
}


abstract production witnessTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in witnessTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "witness " ++ buildWitnesses(ew) ++ ".  ";

  top.toAbella = [witnessTactic(map((.toAbella), ew))];
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = "search.  ";

  top.toAbella = [top];
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = "search " ++ toString(n) ++ ".  ";

  top.toAbella = [top];
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = "search with " ++ sw.pp ++ ".  ";

  top.toAbella = [searchWitnessTactic(sw.toAbella)];
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = "async.  ";

  top.toAbella = [top];
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = "split.  ";

  top.toAbella = [top];
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = "split*.  ";

  top.toAbella = [top];
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = "left.  ";

  top.toAbella = [top];
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = "right.  ";

  top.toAbella = [top];
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = "skip.  ";

  top.toAbella = [top];
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = "abort.  ";

  top.toAbella = [top];
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = "undo.  ";

  top.toAbella = [top];
}


--I have no idea what the arrow does, but there are clears with and without it
abstract production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  top.pp = "clear " ++ (if hasArrow then "-> " else "") ++
           implode(" ", removes) ++ ".  ";

  top.toAbella = [top];
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  top.toAbella = [top];
}


--this assumes newText does NOT include the quotation marks
abstract production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  top.pp = "abbrev " ++ implode(" ", hyps) ++ " \"" ++ newText ++ "\".  ";

  top.toAbella = error("Cannot abbreviate");
}


abstract production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  top.pp = "unabbrev " ++ implode(" ", hyps) ++ "\".  ";

  top.toAbella = error("Cannot abbreviate");
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = "permute " ++ foldr1(\a::String b::String -> a ++ " " ++ b, names) ++
           hypString ++ ".  ";

  top.toAbella = [top];
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  " else ".  ";

  top.toAbella = [top];
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::QName all::Boolean
{
  top.pp = "unfold " ++ id.pp ++ if all then "(all).  " else ".  ";

  top.toAbella = [unfoldIdentifierTactic(id.fullRel, all)];

  top.toAbellaMsgs <- id.relErrors;
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";

  top.toAbella = [top];
}





nonterminal Clearable with
   pp,
   toAbella<Clearable>, toAbellaMsgs,
   proverState;
propagate toAbellaMsgs, proverState, languageCtx on Clearable;

--I don't know what the star is, but some have it
abstract production clearable
top::Clearable ::= star::Boolean hyp::QName instantiation::TypeList
{
  local instString::String =
     if instantiation.pp == ""
     then ""
     else "[" ++ instantiation.pp ++ "]";
  top.pp = (if star then "*" else "") ++ hyp.pp ++ instString;

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
                else head(possibleThms).1, map((.toAbella),
                instantiation));

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





nonterminal ApplyArg with
   pp,
   toAbella<ApplyArg>, toAbellaMsgs,
   languageCtx, proverState;
propagate languageCtx, proverState, toAbellaMsgs on ApplyArg;

abstract production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::TypeList
{
  local instString::String =
     if instantiation.pp == ""
     then ""
     else "[" ++ instantiation.pp ++ "]";
  top.pp = hyp ++ instString;

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

  top.toAbella = starApplyArg(name, instantiation.toAbella);
}





nonterminal EWitness with
   pp,
   languageCtx, proverState,
   toAbella<EWitness>, toAbellaMsgs;
propagate languageCtx, proverState, toAbellaMsgs on EWitness;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;

  top.toAbella = termEWitness(t.toAbella);
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = name ++ " = " ++ t.pp;

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

