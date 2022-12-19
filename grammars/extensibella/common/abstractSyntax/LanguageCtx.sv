grammar extensibella:common:abstractSyntax;

{-
  Information about the current language
-}

nonterminal LanguageCtx with
   currentModule,
   knownNTs, knownProds, knownExtRels, knownFixRels, knownTrans;

synthesized attribute currentModule::QName;
--qualified names of nonterminals in the specification
synthesized attribute knownNTs::[QName];
--[(qualified prod name, args, qualified built NT name)]
synthesized attribute knownProds::[(QName, [Type], QName)];
--[(qualified rel name, args)]
synthesized attribute knownExtRels::[(QName, [Type])];
--[(qualified rel name, args)]
synthesized attribute knownFixRels::[(QName, [Type])];
--[(qualified nonterminal name, args)]
synthesized attribute knownTrans::[(QName, [Type])];

abstract production languageCtx
top::LanguageCtx ::=
   --module in which we are currently working
   currentModule::QName
   --qualified names of nonterminals in the specification
   knownNTs::[QName]
   --[(qualified prod name, args, qualified built NT name)]
   knownProds::[(QName, [Type], QName)] 
   --[(qualified rel name, args)]
   knownExt::[(QName, [Type])]
   --[(qualified rel name, args)]
   knownFix::[(QName, [Type])]
   --[(qualified nonterminal name, args)]
   knownTrans::[(QName, [Type])]
{
  top.currentModule = currentModule;
  top.knownNTs = knownNTs;
  top.knownProds = knownProds;
  top.knownExtRels = knownExt;
  top.knownFixRels = knownFix;
  top.knownTrans = knownTrans;
}


function findNT
[QName] ::= ntName::QName ctx::Decorated LanguageCtx
{
  return filter( if ntName.isQualified
                 then \ q::QName -> q == ntName
                 else \ q::QName -> q.shortName == ntName.shortName,
                ctx.knownNTs);
}


function findProd
[(QName, [Type], QName)] ::= prodName::QName ctx::Decorated LanguageCtx
{
  return filter( if prodName.isQualified
                 then \ p::(QName, [Type], QName) -> p.1 == prodName
                 else \ p::(QName, [Type], QName) ->
                        p.1.shortName == prodName.shortName,
                ctx.knownProds);
}


function findTrans
[(QName, [Type])] ::= ntName::QName ctx::Decorated LanguageCtx
{
  return filter( if ntName.isQualified
                 then \ p::(QName, [Type]) -> p.1 == ntName
                 else \ p::(QName, [Type]) ->
                        p.1.shortName == ntName.shortName,
                ctx.knownTrans);
}


--Boolean is isExtensible (true for ext rel, false for fix rel)
function findRel
[(QName, [Type], Boolean)] ::= relName::QName ctx::Decorated LanguageCtx
{
  local extRels::[(QName, [Type])] =
        filter( if relName.isQualified
                then \ p::(QName, [Type]) -> p.1 == relName
                else \ p::(QName, [Type]) ->
                       p.1.shortName == relName.shortName,
               ctx.knownExtRels);
  local fixRels::[(QName, [Type])] =
        filter( if relName.isQualified
                then \ p::(QName, [Type]) -> p.1 == relName
                else \ p::(QName, [Type]) ->
                       p.1.shortName == relName.shortName,
               ctx.knownFixRels);
  return map(\ p::(QName, [Type]) -> (p.1, p.2, true), extRels) ++
         map(\ p::(QName, [Type]) -> (p.1, p.2, false), fixRels);
}
