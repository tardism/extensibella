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
   thms::[(QName, Metaterm, String)]
{
  top.encode = error("Not done yet");
  top.is_nonextensible = false;

  top.thms = map(\ p::(QName, Metaterm, String) -> (p.1, p.2), thms);
}


--Non-extensible mutuals are written all in one
abstract production nonextensibleTheorem
top::ThmElement ::= name::QName stmt::Metaterm
{
  top.encode =
      [anyTopCommand(theoremDeclaration(name, [], stmt)),
       anyProofCommand(skipTactic())];
  top.is_nonextensible = true;

  top.thms = [(name, stmt)];
}


abstract production splitElement
top::ThmElement ::= toSplit::QName newNames::[QName]
{
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


abstract production kindElement
top::DefElement ::= names::[QName] kind::Kind
{
  --top.encode = [anyTopCommand(kindDeclaration(
}


abstract production typeElement
top::DefElement ::= names::[QName] ty::Type
{

}
