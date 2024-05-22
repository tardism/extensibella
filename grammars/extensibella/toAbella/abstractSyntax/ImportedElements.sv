grammar extensibella:toAbella:abstractSyntax;

nonterminal ThmElement with
   pp,
   encode, is_nonextensible, tag,
   knownThms, thms;

--using AnyCommand allows having a theorem declaration and its proof
synthesized attribute encode::[AnyCommand];
synthesized attribute is_nonextensible::Boolean;
--tag is (numerator, denominator, module)
synthesized attribute tag::(Integer, Integer, String);

--get the theorems produced out of each element
synthesized attribute thms::[(QName, Metaterm)];
--theorems we already know
inherited attribute knownThms::[(QName, Metaterm)];

abstract production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, var bindings, thm statement, induction info)]
   thms::[(QName, Bindings, ExtBody, InductionOns)]
   alsos::[(QName, Bindings, ExtBody, InductionOns)]
   tag::(Integer, Integer, String)
{
  top.pp = text("ExtThm ") ++ ppImplode(text(", "),
                                 map((.pp), map(fst, thms)));

  top.encode = error("extensibleMutualTheoremGroup.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  top.thms =
      map(\ p::(QName, Bindings, ExtBody, InductionOns) ->
            (p.1, p.3.thm), thms ++ alsos);
}


abstract production projectionConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
                    tag::(Integer, Integer, String)
{
  top.pp = text("PC ") ++ name.pp;

  top.encode = error("projectionConstraintTheorem.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  top.thms =
      [(name, bindingMetaterm(forallBinder(), binds, body.thm))];
}


--Non-extensible mutuals are written all in one
abstract production nonextensibleTheorem
top::ThmElement ::= name::QName params::[String] stmt::Metaterm
{
  top.pp = theoremDeclaration(name, params, stmt).pp;

  top.encode =
      [anyTopCommand(theoremDeclaration(name, params, stmt)),
       anyProofCommand(skipTactic())];
  top.is_nonextensible = true;
  top.tag = error("Non-extensible theorem tag");

  top.thms = [(name, stmt)];
}


abstract production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.pp = splitTheorem(toSplit, newNames).pp;

  top.encode = [anyTopCommand(splitTheorem(toSplit, newNames))];
  top.is_nonextensible = true;
  top.tag = error("Non-extensible theorem tag");

  --theorem must already exist, so don't need to consider Maybe
  local foundSplittee::Metaterm =
      lookup(toSplit, top.knownThms).fromJust;
  top.thms = zip(newNames, splitMetaterm(foundSplittee));
}


abstract production extSizeElement
top::ThmElement ::= rels::[(QName, [String])]
                    tag::(Integer, Integer, String)
{
  top.pp = extSizeDeclaration(rels).pp;

  top.encode = error("extSizeElement.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  top.thms =
      flatMap(\ p::(QName, [String]) ->
                buildExtSizeLemmas(p.1, p.2), rels);
}


abstract production projRelElement
top::ThmElement ::= rels::[(QName, [String])]
                    tag::(Integer, Integer, String)
{
  top.pp = projRelDeclaration(rels).pp;

  top.encode = error("projRelElement.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  top.thms =
      flatMap(\ p::(QName, [String]) ->
                buildProjRelLemmas(p.1, p.2), rels);
}


abstract production extIndElement
top::ThmElement ::=
   --[(rel name, rel arg names, full bindings, extra premises)]
   rels::[(QName, [String], Bindings, ExtIndPremiseList)]
   tag::(Integer, Integer, String)
{
  top.pp = text("ExtInd") ++ ppImplode(text(", "),
                                map((.pp), map(fst, rels)));

  top.encode = error("extIndElement.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  --only user-relevant theorems are the lemmas about extSize
  --the proven things are only for framework use
  top.thms =
      flatMap(\ p::(QName, [String], Bindings, ExtIndPremiseList) ->
                buildExtSizeLemmas(p.1, p.2), rels);
}

--Create the contents of Ext_Ind from the tuple of its information
function extIndInfo_to_extIndBody
ExtIndBody ::=
   extIndInfo::[(QName, [String], Bindings, ExtIndPremiseList)]
{
  local p::(QName, [String], Bindings, ExtIndPremiseList) =
      head(extIndInfo);
  local one::ExtIndBody = oneExtIndBody(p.3, p.1, p.2, p.4);
  return
      case extIndInfo of
      | [] -> error("Should not call extIndInfo_to_extIndBody " ++
                    "with empty list")
      | [_] -> one
      | _::t -> branchExtIndBody(one, extIndInfo_to_extIndBody(t))
      end;
}



{-
  The idea is to make the error messages for missing obligations be
  consistent.  Each Prove version of a command checks for exactly the
  type of obligation it expects, then delegates to this in the case
  where that type of obligation is not at the front to get the
  specific error message.
-}
function wrongObligation
Message ::= obligations::[ThmElement]
{
  return
      case obligations of
      | [] -> errorMsg("No obligations left to prove")
      | projectionConstraintTheorem(q, x, b, _)::_ ->
        errorMsg("Expected projection constraint obligation " ++
           justShow(q.pp))
      | extIndElement(relInfo, _)::_ ->
        errorMsg("Expected Ext_Ind obligation for " ++
           implode(", ",
              map(justShow, map((.pp), map(fst, relInfo)))))
      | extSizeElement(relInfo, _)::_ ->
        errorMsg("Expected Ext_Size addition for " ++
           implode(", ",
              map(justShow, map((.pp), map(fst, relInfo)))))
      | projRelElement(relInfo, _)::_ ->
        errorMsg("Expected Proj_Rel addition for " ++
           implode(", ",
              map(justShow, map((.pp), map(fst, relInfo)))))
      | extensibleMutualTheoremGroup(thms, alsos, _)::_ ->
        errorMsg("Expected theorem obligations" ++
           implode(", ", map(justShow, map((.pp), map(fst, thms)))))
      --split these out explicitly for better errors/catching if a new
      --constructor is added
      | nonextensibleTheorem(_, _, _)::_ ->
        error("Nonextensible ThmElement in obligations not cleared")
      | splitElement(_, _)::_ ->
        error("Nonextensible ThmElement in obligations not cleared")
      end;
}





nonterminal DefElement with pp, encode;

abstract production defineElement
top::DefElement ::= defines::[(QName, Type)]
                    --Some clauses don't have bodies, so Maybe
                    clauses::[(QName, TermList, Maybe<Metaterm>)]
{
  top.pp = definitionDeclaration(defines, defs).pp;

  local defs::Defs =
        foldrLastElem(consDefs, singleDefs,
           map(\ p::(QName, TermList, Maybe<Metaterm>) ->
                 case p of
                 | (q, a, nothing()) -> factDef(q, a)
                 | (q, a, just(b)) -> ruleDef(q, a, b)
                 end,
               clauses));
  top.encode = [anyTopCommand(definitionDeclaration(defines, defs))];
}


abstract production codefineElement
top::DefElement ::= defines::[(QName, Type)]
                    --Some clauses don't have bodies, so Maybe
                    clauses::[(QName, TermList, Maybe<Metaterm>)]
{
  top.pp = codefinitionDeclaration(defines, defs).pp;

  local defs::Defs =
        foldrLastElem(consDefs, singleDefs,
           map(\ p::(QName, TermList, Maybe<Metaterm>) ->
                 case p of
                 | (q, a, nothing()) -> factDef(q, a)
                 | (q, a, just(b)) -> ruleDef(q, a, b)
                 end,
               clauses));
  top.encode =
      [anyTopCommand(codefinitionDeclaration(defines, defs))];
}


abstract production kindElement
top::DefElement ::= names::[QName] kind::Kind
{
  top.pp = kindDeclaration(names, kind).pp;
  top.encode = [anyTopCommand(kindDeclaration(names, kind))];
}


abstract production typeElement
top::DefElement ::= names::[QName] ty::Type
{
  top.pp = typeDeclaration(names, ty).pp;
  top.encode = [anyTopCommand(typeDeclaration(names, ty))];
}
