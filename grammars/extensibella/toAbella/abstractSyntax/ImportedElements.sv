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
   --[(thm name, var bindings, thm statement, induction measure, IH name)]
   thms::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   alsos::[(QName, Bindings, ExtBody, String, Maybe<String>)]
   tag::(Integer, Integer, String)
{
  top.pp = text("ExtThm ") ++ ppImplode(text(", "),
                                 map((.pp), map(fst, thms)));

  top.encode = error("extensibleMutualTheoremGroup.encode");
  top.is_nonextensible = false;
  top.tag = tag;

  top.thms =
      map(\ p::(QName, Bindings, ExtBody, String, Maybe<String>) ->
            (p.1, p.3.thm), thms ++ alsos);
}


abstract production translationConstraintTheorem
top::ThmElement ::= name::QName binds::Bindings body::ExtBody
                    tag::(Integer, Integer, String)
{
  top.pp = text("TC ") ++ name.pp;

  top.encode = error("translationConstraintTheorem.encode");
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
