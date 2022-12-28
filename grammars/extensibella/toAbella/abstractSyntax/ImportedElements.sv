grammar extensibella:toAbella:abstractSyntax;

nonterminal ThmElement with
   pp,
   encode, is_nonextensible,
   knownThms, thms;

--using AnyCommand allows having a theorem declaration and its proof
synthesized attribute encode::[AnyCommand];
synthesized attribute is_nonextensible::Boolean;

--get the theorems produced out of each element
synthesized attribute thms::[(QName, Metaterm)];
--theorems we already know
inherited attribute knownThms::[(QName, Metaterm)];

abstract production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, thm statement, induction measure)]
   thms::[(QName, ExtBody, String)]
{
  top.pp = error("extensibleMutualTheoremGroup.pp");

  top.encode = error("extensibleMutualTheoremGroup.encode");
  top.is_nonextensible = false;

  top.thms =
      map(\ p::(QName, ExtBody, String) -> (p.1, p.2.thm), thms);
}


--Non-extensible mutuals are written all in one
abstract production nonextensibleTheorem
top::ThmElement ::= name::QName stmt::Metaterm
{
  top.pp = theoremDeclaration(name, [], stmt).pp;

  top.encode =
      [anyTopCommand(theoremDeclaration(name, [], stmt)),
       anyProofCommand(skipTactic())];
  top.is_nonextensible = true;

  top.thms = [(name, stmt)];
}


abstract production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
  top.pp = splitTheorem(toSplit, newNames).pp;

  top.encode = [anyTopCommand(splitTheorem(toSplit, newNames))];
  top.is_nonextensible = true;

  --theorem must already exist, so don't need to consider Maybe
  local foundSplittee::Metaterm =
      lookup(toSplit, top.knownThms).fromJust;
  top.thms = zipWith(pair, newNames, splitMetaterm(foundSplittee));
}





nonterminal DefElement with pp, encode;

abstract production defineElement
top::DefElement ::= defines::[(QName, Type)]
                    --Some clauses don't have bodies, so Maybe
                    clauses::[(Metaterm, Maybe<Metaterm>)]
{
  top.pp = definitionDeclaration(defines, defs).pp;

  local defs::Defs =
        foldrLastElem(consDefs, singleDefs,
           map(\ p::(Metaterm, Maybe<Metaterm>) ->
                 case p of
                 | (m, nothing()) -> factDef(m)
                 | (m, just(b)) -> ruleDef(m, b)
                 end,
               clauses));
  top.encode = [anyTopCommand(definitionDeclaration(defines, defs))];
}


abstract production codefineElement
top::DefElement ::= defines::[(QName, Type)]
                    --Some clauses don't have bodies, so Maybe
                    clauses::[(Metaterm, Maybe<Metaterm>)]
{
  top.pp = codefinitionDeclaration(defines, defs).pp;

  local defs::Defs =
        foldrLastElem(consDefs, singleDefs,
           map(\ p::(Metaterm, Maybe<Metaterm>) ->
                 case p of
                 | (m, nothing()) -> factDef(m)
                 | (m, just(b)) -> ruleDef(m, b)
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
