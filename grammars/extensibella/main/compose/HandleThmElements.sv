grammar extensibella:main:compose;

--modules and their remaining commands before handling this element
inherited attribute incomingMods::[(QName, DecCmds)] occurs on ThmElement;
--modules and their remaining commands after handling this element
synthesized attribute outgoingMods::[(QName, DecCmds)] occurs on ThmElement;
--commands to handle this element
synthesized attribute composedCmds::String occurs on ThmElement;

--pass in environments in MWDA-approved ways
inherited attribute relEnv::Env<RelationEnvItem> occurs on ThmElement;
inherited attribute constrEnv::Env<ConstructorEnvItem> occurs on ThmElement;
inherited attribute tyEnv::Env<TypeEnvItem> occurs on ThmElement;

--build the definitions for R_ES and R_T
synthesized attribute extIndDefs::[String] occurs on ThmElement;
aspect default production
top::ThmElement ::=
{
  top.extIndDefs = [];
}

aspect production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, var bindings, thm statement, induction measure, IH name)]
   thms::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   alsos::[(QName, Bindings, ExtBody, String, Maybe<String>)]
{
  local multiple::Boolean = length(thms) + length(alsos) > 1;
  local extName::QName =
      if multiple
      then toQName("$extThm_" ++ toString(genInt()))
      else fst(head(thms));
  local extThms::ExtThms =
      foldr(\ p::(QName, Bindings, ExtBody, String, Maybe<String>)
              rest::ExtThms ->
              addExtThms(p.1, p.2, p.3, p.4, p.5, rest),
            endExtThms(), thms ++ alsos);
  extThms.relationEnv = top.relEnv;
  extThms.constructorEnv = top.constrEnv;
  extThms.typeEnv = top.tyEnv;
  extThms.expectedIHNum = 0;

  local declare::String =
      "Theorem " ++ extName.abella_pp ++ " : " ++
      extThms.toAbella.abella_pp ++ ".\n";
  local inductions::String =
      "induction on " ++
      implode(" ", map(toString, extThms.inductionNums)) ++ ".\n";
  local renames::String =
      implode(" ",
         map(\ p::(String, String, String) ->
               "rename " ++ p.1 ++ " to " ++ p.2 ++ ".",
             extThms.renamedIHs));

  local after::String =
      if multiple
      then "Split " ++ extName.abella_pp ++ " as " ++
           implode(", ",
                   map((.abella_pp),
                       map(fst, thms) ++ map(fst, alsos))) ++ ".\n"
      else "";

  top.composedCmds =
      declare ++ inductions ++ renames ++ " skip.\n" ++ after ++ "\n\n";


  top.outgoingMods =
      dropAllOccurrences(top.incomingMods, map(fst, thms));
}


aspect production translationConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
{
  --MWDA copy of body
  local bodyC::ExtBody = body;
  bodyC.relationEnv = top.relEnv;
  bodyC.constructorEnv = top.constrEnv;
  bodyC.typeEnv = top.tyEnv;
  bodyC.boundNames = binds.usedNames;

  local tcMods::[(QName, DecCmds)] =
      getAllOccurrences(top.incomingMods, [name]);
  --first contains declaration and set-up
  local startPrf::String =
      case head(tcMods).2 of
      | addRunCommands(c, _) ->
        --set-up for translation constraint, including declaration
        implode("", map((.abella_pp), c.toAbella))
      | _ -> error("Must be translationConstraint first")
      end;
  --rest of list provides the rest of the proof
  local restPrf::String =
      implode("", map(\ p::(QName, DecCmds) -> getProof(p.2).2,
                      tail(tcMods)));
  top.composedCmds = startPrf ++ " " ++ restPrf ++ "\n\n";

  --took these proofs, so drop them
  top.outgoingMods = dropAllOccurrences(top.incomingMods, [name]);
}


aspect production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  local declaration::String =
      "Theorem " ++ name.abella_pp ++
      (if null(params) then ""
                       else "[" ++ implode(", ", params) ++ "]") ++
      " : " ++ stmt.abella_pp ++ ".\n";

  local updatePair::([(QName, DecCmds)], String) =
      updateMod(top.incomingMods, name.moduleName, getProof);

  top.outgoingMods = updatePair.1;
  top.composedCmds = declaration ++ updatePair.2 ++ "\n\n";
}


aspect production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.composedCmds =
      "Split " ++ toSplit.abella_pp ++ " as " ++
      implode(", ", map((.abella_pp), newNames)) ++ ".\n\n";
  top.outgoingMods =
      updateMod(top.incomingMods, head(newNames).moduleName,
                \ c::DecCmds -> (dropFirstTopCommand(c), "")).1;
}


aspect production extIndElement
top::ThmElement ::=
   --[(rel name, rel arg names, trans args, trans ty,
   --    original, translated name)]
   rels::[(QName, [String], [Term], QName, String, String)]
{
  {-
    Definitions of R_{ES} and R_T relations
  -}
  local extSizeDef::String =
      buildExtSize(map(fst, rels), top.relEnv).abella_pp;
  local transRelDef::String =
      buildTransRel(rels, top.relEnv).abella_pp;
  top.extIndDefs = [extSizeDef, transRelDef];


  --get the information we need about the relation clauses to build
  --   the individual proofs
  --[[(number of adds, [(1-based indices for R_{ES} premises,
  --                     0-based IH indices)], is host)]]
  --inner list is grouped by relation
  --   (e.g. [[rel 1 clauses], [rel 2 clauses], ...])
  local clauseInfo::[[(Integer, [(Integer, Integer)], Boolean)]] =
      map(\ q::QName ->
            let rel::RelationEnvItem =
                decorate q with {relationEnv=top.relEnv;}.fullRel
            in --[(extension clause or not, split-up body)]
            let splits::[(Boolean, [Metaterm])] =
                map(\ d::([Term], Maybe<Metaterm>) ->
                      (!sameModule(q.moduleName,
                           elemAtIndex(d.1, rel.pcIndex
                                      ).headConstructor),
                       case d.2 of
                       | nothing() -> []
                       | just(bindingMetaterm(_, _, m)) ->
                         m.splitConjunctions
                       | just(m) -> m.splitConjunctions
                       end),
                    rel.defsList)
            in --premises that are part of this group of rels
            let hereRels::[(Boolean, [Integer])] =
                map(\ l::(Boolean, [Metaterm]) ->
                      (l.1,
                       map(\ m::Metaterm ->
                             case m of
                             | relationMetaterm(q, _, _)
                               when contains(q, map(fst, rels)) ->
                               indexOfName(q, rels) --index of IH
                             | _ -> -1
                             end,
                          l.2)),
                    splits)
            in
              map(\ l::(Boolean, [Integer]) ->
                    let plusCount::Integer =
                        length(filter(\ x -> x >= 0, l.2)
                              ) - if !l.1 then 1 else 0
                    in
                      (plusCount,
                       filterMap(\ p::(Integer, Integer) ->
                                   if p.2 >= 0
                                   then just(p)
                                   else nothing(),
                          enumerateFrom(plusCount + 1, l.2)),
                       !l.1)
                    end,
                  hereRels)
            end end end,
          map(fst, rels));

  {-
    Lemmas about R_{ES}
  -}
  local lemmaStatements::[[(QName, Metaterm)]] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            buildExtSizeLemmas(p.1, p.2),
          rels);
  local jointLemmaNames::(String, String, String) =
      --first make a sanity/extension check
      if length(head(lemmaStatements)) != 3
      then error("Number of ExtSize lemmas must be 3")
      else case lemmaStatements of
           | [[a, b, c]] -> --only one rel, so use actual names
             (a.1.abella_pp, b.1.abella_pp, c.1.abella_pp)
           | _ -> --multiple rels together, so use fake then split
             ("$extIndThm_" ++ toString(genInt()),
              "$extIndThm_" ++ toString(genInt()),
              "$extIndThm_" ++ toString(genInt()))
           end;
  --leave it as a list because Silver pairs of pairs don't really work
  local provingLemmaStatements::[(String, Metaterm)] =
      [
       (jointLemmaNames.1,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(l).2,
                   lemmaStatements))),
       (jointLemmaNames.2,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(tail(l)).2,
                   lemmaStatements))),
       (jointLemmaNames.3,
        foldr1(andMetaterm,
               map(\ l::[(QName, Metaterm)] -> head(tail(tail(l))).2,
                   lemmaStatements)))
      ];
  local lemmaInduction::String =
      "induction on " ++
      implode(" ", repeat("1",
                      length(lemmaStatements))) ++ "." ++
      if length(lemmaStatements) == 1
      then "\n" else " split.\n";
  local lemmaPrfParts::[[(String, String, String)]] =
      map(--[(plus count, [(ES premise, IH num)], is host)]
        \ l::[(Integer, [(Integer, Integer)], Boolean)] ->
          map(
            \ p::(Integer, [(Integer, Integer)], Boolean) ->
              let basicPrf::String =
                  implode("",
                     map(\ ip::(Integer, Integer) ->
                           " apply IH" ++ (if ip.2 == 0 then ""
                                           else toString(ip.2)) ++
                           " to ES" ++ toString(ip.1) ++ ".",
                         p.2))
              in
              let r::[Integer] = range(1, p.1 + 1)
              in
                 --non-negative
                (basicPrf ++
                 foldr(\ i::Integer rest::String ->
                         rest ++ " apply extensibella-$-stdLib-$-" ++
                         "lesseq_integer__add_positive to _ _ ES" ++
                         toString(i) ++ ".", "",
                       r) ++ " search.\n",
                 --is_integer
                 basicPrf ++
                 foldr(\ i::Integer rest::String ->
                         rest ++ " apply extensibella-$-stdLib-$-" ++
                         "plus_integer_is_integer to _ _ ES" ++
                         toString(i) ++ ".", "",
                       r) ++ " search.\n",
                 --dropT
                 basicPrf ++ " search.\n")
                end end,
            l),
          clauseInfo);
  local lemmaPrfs::(String, String, String) =
      foldr(\ l::[(String, String, String)]
              rest::(String, String, String) ->
              let sub::(String, String, String) =
                foldr(\ here::(String, String, String)
                        rest::(String, String, String) ->
                        (here.1 ++ rest.1, here.2 ++ rest.2,
                         here.3 ++ rest.3),
                      rest, l)
              in
                ("intros ES. ES1: case ES.\n" ++ sub.1,
                 "intros ES. ES1: case ES.\n" ++ sub.2,
                 "intros ES. ES1: case ES.\n" ++ sub.3)
              end,
            ("", "", ""), lemmaPrfParts);
  local endLemmaCommands::String =
      if length(lemmaStatements) == 1
      then "" --nothing to split
      else "\n" ++
           "Split " ++ jointLemmaNames.1 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] -> head(l).1,
                         lemmaStatements))) ++ ".\n" ++
           "Split " ++ jointLemmaNames.2 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] -> head(tail(l)).1,
                         lemmaStatements))) ++ ".\n" ++
           "Split " ++ jointLemmaNames.3 ++ " as " ++
              implode(", ",
                 map((.abella_pp),
                     map(\ l::[(QName, Metaterm)] ->
                           head(tail(tail(l))).1,
                         lemmaStatements))) ++ ".\n";
  local fullLemmas::String =
      "Theorem " ++ head(provingLemmaStatements).1 ++ " : " ++
         head(provingLemmaStatements).2.abella_pp ++ ".\n" ++
         lemmaInduction ++ lemmaPrfs.1 ++ "\n" ++
      "Theorem " ++ head(tail(provingLemmaStatements)).1 ++ " : " ++
         head(tail(provingLemmaStatements)).2.abella_pp ++ ".\n" ++
         lemmaInduction ++ lemmaPrfs.2 ++ "\n" ++
      "Theorem " ++ head(tail(tail(provingLemmaStatements))).1 ++
         " : " ++ head(tail(tail(provingLemmaStatements))
                                ).2.abella_pp ++
         ".\n" ++ lemmaInduction ++ lemmaPrfs.3 ++
       endLemmaCommands;

  {-
    R to R_{ES} proof
  -}
  local toExtSizeStatement::Metaterm =
      foldr1(andMetaterm,
         map(\ p::(QName, [String], [Term], QName, String, String) ->
               let num::String = freshName("N", p.2)
               in
                 bindingMetaterm(forallBinder(),
                    toBindings(p.2),
                    impliesMetaterm(
                       relationMetaterm(p.1,
                          toTermList(map(basicNameTerm, p.2)),
                          emptyRestriction()),
                       bindingMetaterm(existsBinder(),
                          toBindings([num]),
                          relationMetaterm(extSizeQName(p.1.sub),
                             toTermList(map(basicNameTerm, p.2 ++ [num])),
                             emptyRestriction()))))
               end,
             rels));
  local toExtSizeNames::[String] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            "$toExtSize__" ++ p.1.abella_pp,
          rels);
  local toExtSizeProveName::String =
      if length(toExtSizeNames) == 1
      then head(toExtSizeNames)
      else "$toExtSize_" ++ toString(genInt());
  local toExtSizeProofStart::String =
      "induction on " ++ implode(" ", repeat("1", length(rels))) ++
      ". rename IH to IH0." ++ --simplifies building the proof code
      if length(rels) > 1 then " split." else "";
  local toExtSizeProofs::[String] =
      map(
        \ l::[(Integer, [(Integer, Integer)], Boolean)] ->
          " intros R. R1: case R.\n  " ++
          implode("\n  ",
             map(--(plus count, [(R premise, IH num)], is host)
               \ p::(Integer, [(Integer, Integer)], Boolean) ->
                         --[(hyp name, application, IH num)]
                 let appIHs::[(String, String, Integer)] =
                     map(\ ip::(Integer, Integer) ->
                           let hyp::String =
                               "ES" ++ toString(genInt())
                           in
                             (hyp,
                              hyp ++ ": apply IH" ++ toString(ip.2) ++
                              --subtract to get back to R indices from
                              --R_{ES} indices
                              " to R" ++ toString(ip.1 - p.1) ++ ".",
                              ip.2)
                           end, p.2)
                 in       --[(hyp name, application)]
                 let appIses::[(String, String)] =
                     map(\ ep::(String, String, Integer) ->
                           let hyp::String =
                               "Is" ++ toString(genInt())
                           in
                             (hyp,
                              hyp ++ ": apply " ++
                              head(tail(elemAtIndex(lemmaStatements,
                                           ep.3))).1.abella_pp ++
                              " to " ++ ep.1 ++ ".")
                           end, appIHs)
                 in
                 let adds::String =
                     foldl(--(hyp name, application)
                        \ rest::(String, String) isp::(String, String) ->
                          let plusHyp::String =
                              "Plus" ++ toString(genInt())
                          in
                          let isHyp::String =
                              "Is" ++ toString(genInt())
                          in
                            (isHyp,
                             rest.2 ++ " " ++
                             plusHyp ++ ": apply " ++
                                "extensibella-$-stdLib-$-" ++
                                "plus_integer_total to " ++ rest.1 ++
                                " " ++ isp.1 ++ ". " ++
                             isHyp ++ ": apply " ++
                                "extensibella-$-stdLib-$-" ++
                                "plus_integer_is_integer to _ _ " ++
                                plusHyp ++ ".")
                          end end,
                        (head(appIses).1, ""), tail(appIses)).2
                 in
                   if null(p.2) then "search."
                   else
                     implode(" ",
                        map(\ p::(String, String, Integer) -> p.2,
                            appIHs)) ++ " " ++
                     implode(" ", map(\ p::(String, String) -> p.2,
                                      appIses)) ++ " " ++
                     adds ++ " search."
                 end end end, l)),
        clauseInfo);
  local afterToExtSize::String =
      if length(toExtSizeNames) == 1
      then "" --nothing to split
      else "Split " ++ toExtSizeProveName ++ " as " ++
           implode(", ", toExtSizeNames) ++ ".\n";
  local fullToExtSize::String =
      "Theorem " ++ toExtSizeProveName ++ " : " ++
      toExtSizeStatement.abella_pp ++ ".\n" ++
      toExtSizeProofStart ++ "\n" ++
      implode("\n", toExtSizeProofs) ++ "\n" ++
      afterToExtSize;

  {-
    R_{ES} to R_T proof
  -}
  local toTransRelStatement::Metaterm =
     foldr1(andMetaterm,
        map(\ p::(QName, [String], [Term], QName, String, String) ->
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
              end,
            rels));
  local toTransRelNames::[String] =
      map(\ p::(QName, [String], [Term], QName, String, String) ->
            "$toTransRel__" ++ p.1.abella_pp,
          rels);
  local toTransRelProveName::String =
      if length(toTransRelNames) == 1
      then head(toTransRelNames)
      else "$toTransRel_" ++ toString(genInt());
  local toTransRelProofStart::String =
      "induction on " ++ implode(" ", repeat("2", length(rels))) ++
      ". induction on " ++ implode(" ", repeat("1", length(rels))) ++
      "." ++ if length(rels) > 1 then " split.\n" else "\n";
  local toTransRelHostProofs::[String] =
      map(\ l::[(Integer, [(Integer, Integer)], Boolean)] ->
            " intros Rel Acc. Rel: case Rel (keep).\n  " ++
            implode("\n  ",
               filterMap(--(plus count, [(Rel premise, IH num)], is host)
                 \ p::(Integer, [(Integer, Integer)], Boolean) ->
                   --note all nums are >= 0, is_integer
                   let appPos::[String] =
                       map(
                         \ ip::(Integer, Integer) ->
                           let lemmas::[(QName, Metaterm)] =
                               elemAtIndex(lemmaStatements, ip.2)
                           in
                             "apply " ++ head(lemmas).1.abella_pp ++
                                " to Rel" ++ toString(ip.1) ++ ". " ++
                             "apply " ++ head(tail(lemmas)).1.abella_pp ++
                                " to Rel" ++ toString(ip.1) ++ "."
                           end, p.2)
                   in --note all summed numbers are >= 0, is_integer
                   let addPos::[String] =
                       map(\ i::Integer ->
                             "apply extensibella-$-stdLib-$-" ++
                                "lesseq_integer__add_positives to " ++
                                "_ _ Rel" ++ toString(i) ++ ". " ++
                             "apply extensibella-$-stdLib-$-" ++
                                "plus_integer_is_integer to " ++
                                "_ _ Rel" ++ toString(i) ++ ".",
                           range(1, p.1 + 1))
                   in --apply lte_left/lte_right to all additions
                      --[(left result hyp, right result hyp, applications)]
                   let ltes::[(String, String, String)] =
                       reverse(
                         map(\ i::Integer ->
                               let leftHyp::String =
                                   "LE_L" ++ toString(genInt())
                               in
                               let rightHyp::String =
                                   "LE_R" ++ toString(genInt())
                               in
                                 (leftHyp, rightHyp,
                                  rightHyp ++ ": apply extensibella-$-" ++
                                     "stdLib-$-lte_right to Rel" ++
                                     toString(i) ++ " _ _ _. " ++
                                  leftHyp ++ ": apply extensibella-$-" ++
                                     "stdLib-$-lte_left to Rel" ++
                                     toString(i) ++ " _ _ _.")
                               end end, range(1, p.1 + 1)))
                   in --([relevent <= hyps for IH usage], applications)
                   let transes::([String], String) =
                       if p.1 == 0
                       then --assume there is one R_{ES} premise if here
                            --we need the <= final N with a name for
                            --   this, so redo is here to name it
                            let h::String = "LE" ++ toString(genInt())
                            in
                            let is::String = "IS" ++ toString(genInt())
                            in
                              ([h],
                               is ++ ": apply " ++
                                 head(tail(elemAtIndex(lemmaStatements,
                                         head(p.2).2))).1.abella_pp ++
                                 " to Rel" ++ toString(head(p.2).1) ++
                                 "." ++
                               h ++ ": apply extensibella-$-stdLib" ++
                                 "-$-is_integer_lesseq to " ++ is ++ ".")
                            end end
                       else foldl(
                              \ rest::([String], String)
                                here::(String, String, String) ->
                                let leftHyp::String =
                                    "LE" ++ toString(genInt())
                                in
                                let rightHyp::String =
                                    "LE" ++ toString(genInt())
                                in --drop first in rest.1 because it is
                                   --for a sum, not an R_{ES} num
                                  (leftHyp::rightHyp::tail(rest.1),
                                   rest.2 ++
                                   leftHyp ++ ": apply extensibella" ++
                                      "-$-stdLib-$-lesseq_integer_" ++
                                      "transitive to " ++ here.1 ++
                                      " " ++ head(rest.1) ++ ". " ++
                                   rightHyp ++ ": apply extensibella" ++
                                      "-$-stdLib-$-lesseq_integer_" ++
                                      "transitive to " ++ here.2 ++
                                      " " ++ head(rest.1) ++ ". ")
                                end end,
                              ([head(ltes).1, head(ltes).2], ""),
                              tail(ltes))
                   in
                   {-
                     My initial plan was to apply the IH with "_" for
                     the acc premise, but that doesn't work because it
                     has an inductive restriction.  Because it needs
                     to be filled at application time, but by what
                     depends on cases, we either need to nest as we
                     have done belowe (i.e. rest appears in both
                     branches), or assert the conclusion of the IH to
                     avoid nesting.  We can't assert the conclusion
                     because we don't know what it is without live
                     Abella here, so we nest it.  This isn't too
                     inefficient in practice, as there shouldn't be
                     more than ~3 premises, so ease of implementation
                     wins over cutting out a handful of commands.
                   -}
                   let appIHs::String =
                     let a::String = "A" ++ toString(genInt())
                     in
                       a ++ ": case Acc (keep). " ++
                       foldr(--(0 <= N, Rel premise, IH num)
                          \ t::(String, Integer, Integer) rest::String ->
                            let or::String = "Or" ++ toString(genInt())
                            in
                            let l::String = "L" ++ toString(genInt())
                            in
                            let aa::String = "A" ++ toString(genInt())
                            in --second IH, so len(rels) (number in first
                               --   IH set) + t.3 (offset into second set)
                            let ih::String =
                                "IH" ++ toString(length(rels) + t.3)
                            in
                              --split <= into < \/ =
                              or ++ ": apply extensibella-$-stdLib" ++
                                 "-$-lesseq_integer_less_or_eq to " ++
                                 t.1 ++ ". " ++
                              --split into cases
                              l ++ ": case " ++ or ++ ". " ++
                              -- <:  create new acc
                              aa ++ ": apply " ++ a ++ " to _ " ++
                                 l ++ ". " ++
                              "apply " ++ ih ++ " to Rel" ++
                                 toString(t.2) ++ " " ++ aa ++ ". " ++
                              rest ++
                              -- =:  use this acc
                              " apply " ++ ih ++ " to Rel" ++
                                 toString(t.2) ++ " Acc. " ++
                              rest
                            end end end end,
                           "search.", zip(transes.1, p.2))
                     end
                   in
                     if !p.3 --is host
                     then nothing()
                     else if length(p.2) == 0
                     then just("search.")
                     else just(
                            implode(" ", appPos) ++ " " ++
                            implode(" ", addPos) ++ " " ++
                            implode(" ",
                               map(\ p::(String, String, String) ->
                                     p.3, ltes)) ++ " " ++
                            transes.2 ++ appIHs)
                   end end end end end, l)),
          clauseInfo);
  local afterToTransRel::String =
      if length(toTransRelNames) == 1
      then "" --nothing to split
      else "Split " ++ toTransRelProveName ++ " as " ++
           implode(", ", toTransRelNames) ++ ".\n";
  local fullToTransRel::String =
      "Theorem " ++ toTransRelProveName ++ " : " ++
      toTransRelStatement.abella_pp ++ ".\n" ++
      toTransRelProofStart ++
      implode("\n", toTransRelHostProofs) ++ "\n" ++
      "skip.\n" ++ afterToTransRel;

  {-
    R to R_T proof
  -}
  local extIndProofs::[String] =
      map(\ p::(Integer, QName, [String], [Term], QName,
                         String, String) ->
            let stmt::Metaterm =
                bindingMetaterm(forallBinder(),
                   toBindings(p.3),
                   impliesMetaterm(
                      relationMetaterm(p.2,
                         toTermList(map(basicNameTerm, p.3)),
                         emptyRestriction()),
                      relationMetaterm(transRelQName(p.2.sub),
                         toTermList(map(basicNameTerm, p.3)),
                         emptyRestriction())))
            in
              "Theorem " ++ extIndThmName(p.2) ++ " : " ++
                 stmt.abella_pp ++ ".\n" ++
              --make R_{ES}
              "intros R. ES: apply " ++
                 elemAtIndex(toExtSizeNames, p.1) ++ " to R.\n" ++
              --make acc N
              let lemmas::[(QName, Metaterm)] =
                  elemAtIndex(lemmaStatements, p.1)
              in
                "P: apply " ++ head(lemmas).1.abella_pp ++
                   " to ES. " ++
                "Is: apply " ++ head(tail(lemmas)).1.abella_pp ++
                   " to ES. " ++
                "A: apply extensibella-$-stdLib-$-all_acc to Is P.\n"
              end ++
              --make R_T
              "apply " ++ elemAtIndex(toTransRelNames, p.1) ++
                 " to ES A. search."
            end,
          enumerate(rels));


  top.composedCmds = fullLemmas ++ "\n" ++ fullToExtSize ++ "\n" ++
      fullToTransRel ++ "\n" ++ implode("\n", extIndProofs) ++ "\n\n\n";

  top.outgoingMods =
      dropExtInd(top.incomingMods, map(fst, rels));
}

--to get consistent names
function extIndThmName
String ::= rel::QName
{
  return "$extInd_" ++ rel.abella_pp;
}


function indexOfName
Integer ::= q::QName l::[(QName, a)]
{
  return case l of
         | [] -> error("not in list")
         | (x, _)::_ when x == q -> 0
         | _::rest -> indexOfName(q, rest) + 1
         end;
}





----------------------------------------------------------------------
-- Helper functions
----------------------------------------------------------------------

--update a module in the list with the update function, returning the
--   produced string
--does not change the order of modules, just updates one
function updateMod
([(QName, DecCmds)], String) ::= mods::[(QName, DecCmds)] mod::QName
                                 update::((DecCmds, String) ::= DecCmds)
{
  return case mods of
         | [] -> error("Module not in module map")
         | (q, c)::rest when q == mod ->
           let p::(DecCmds, String) = update(c)
           in
             ((q, p.1)::rest, p.2)
           end
         | (q, c)::rest ->
           let p::([(QName, DecCmds)], String) =
               updateMod(rest, mod, update)
           in
             ((q, c)::p.1, p.2)
           end
         end;
}


--drop the first top command in a sequence of commands, including its
--   proof if it has one
--assumes the commands start with a top command
function dropFirstTopCommand
DecCmds ::= c::DecCmds
{
  return
      case c of
      | emptyRunCommands() -> error("dropFirstTopCommand(empty)")
      | addRunCommands(a, r) -> dropFirstTopCommand_help(r)
      end;
}
function dropFirstTopCommand_help
DecCmds ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> c
         | addRunCommands(anyTopCommand(t), r) -> c
         | addRunCommands(_, r) ->
           dropFirstTopCommand_help(r)
         end;
}


--get the next proof, dropping it from the cmds
--assumes it starts with one top command
function getProof
(DecCmds, String) ::= c::DecCmds
{
  return
      case c of
      | emptyRunCommands() -> error("getProof(empty)")
      | addRunCommands(a, r) -> getProof_help(r)
      end;
}
function getProof_help
(DecCmds, String) ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> (c, "")
         | addRunCommands(anyTopCommand(t), r) -> (c, "")
         | addRunCommands(anyProofCommand(p), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
           let f::[ProofCommand] = p.toAbella
           in
             (rest.1, implode("", map((.abella_pp), f)) ++ rest.2)
           end end
         | addRunCommands(anyNoOpCommand(n), r) ->
           let rest::(DecCmds, String) = getProof_help(r)
           in
             (rest.1, n.full.abella_pp ++ rest.2)
           end
         | addRunCommands(anyParseFailure(e), r) ->
           error("How did this get here?")
         end;
}


--get all the modules where thms is the first thing
function getAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, c)::getAllOccurrences(r, thms)
           | _ -> getAllOccurrences(r, thms)
           end
         end;
}


--drop the declaration and proof of thms in every module starting with them
function dropAllOccurrences
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] thms::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | emptyRunCommands() ->
             (q, c)::dropAllOccurrences(r, thms)
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesNames(thms) ->
             (q, dropFirstTopCommand(c))::dropAllOccurrences(r, thms)
           | addRunCommands(a, _) ->
             (q, c)::dropAllOccurrences(r, thms)
           end
         end;
}
--same, but for Ext_Ind and Prove_Ext_Ind
function dropExtInd
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)] rels::[QName]
{
  return case mods of
         | [] -> []
         | (q, c)::r ->
           case c of
           | emptyRunCommands() ->
             (q, c)::dropExtInd(r, rels)
           | addRunCommands(anyTopCommand(t), _)
             when t.matchesRels(rels) ->
             (q, dropFirstTopCommand(c))::dropExtInd(r, rels)
           | addRunCommands(a, _) ->
             (q, c)::dropExtInd(r, rels)
           end
         end;
}


--clear out all the non-proof things at the front of files
function dropNonProof
[(QName, DecCmds)] ::= mods::[(QName, DecCmds)]
{
  return case mods of
         | [] -> []
         | (q, c)::r -> (q, dropNonProof_oneMod(c))::dropNonProof(r)
         end;
}
function dropNonProof_oneMod
DecCmds ::= c::DecCmds
{
  return case c of
         | emptyRunCommands() -> c
         | addRunCommands(anyTopCommand(t), r) when t.isNotProof ->
           dropNonProof_oneMod(dropFirstTopCommand(c))
         | _ -> c
         end;
}





{-
  Why an attribute pointing to a function instead of a set of
  attributes?  We're accessing this on decorated trees.  We cannot
  redecorate them to give them inherited attributes with the original
  map, so we use the functions to handle the actual work.
-}
--checks whether the given names are part of this one
synthesized attribute matchesNames::(Boolean ::= [QName])
   occurs on TopCommand;
--checks whether the given relations are part of this ExtInd
synthesized attribute matchesRels::(Boolean ::= [QName])
   occurs on TopCommand;

--false if a proof element, true otherwise
synthesized attribute isNotProof::Boolean occurs on TopCommand;

aspect default production
top::TopCommand ::=
{
  top.matchesRels = \ _ -> false;
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms alsos::ExtThms
{
  top.matchesNames =
      \ l::[QName] ->
        !null(intersect(l, map(fst, thms.provingTheorems)));

  top.isNotProof = false;
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  top.matchesNames = \ l::[QName] -> !null(intersect(l, names));

  top.isNotProof = false;
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.matchesNames = \ l::[QName] -> head(l) == fullName;

  top.isNotProof = false;
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.matchesNames = \ l::[QName] -> head(l) == name;

  top.isNotProof = false;
}


aspect production extIndDeclaration
top::TopCommand ::= body::ExtIndBody
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels =
      \ l::[QName] -> !null(intersect(l, body.relations));

  top.isNotProof = false;
}


aspect production proveExtInd
top::TopCommand ::= rels::[QName]
{
  top.matchesNames = \ l::[QName] -> false;

  top.matchesRels = \ l::[QName] -> !null(intersect(rels, l));

  top.isNotProof = false;
}


aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.matchesNames = \ l::[QName] -> head(l) == fullName;

  top.isNotProof = false;
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  --won't use this for split, since that isn't distributed
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = false;
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.matchesNames = \ l::[QName] -> false;

  top.isNotProof = true;
}
