grammar extensibella:common:abstractSyntax;

nonterminal QName with
   pp,
   languageCtx,
   shortName, moduleName, isQualified,
   addBase, baseAdded,
   ntErrors, ntFound, fullNT,
   prodErrors, prodFound, fullProd, prodArgs, prodBuilds,
   transErrors, transFound, fullTransNT, transType,
   relErrors, relFound, fullRel, relArgs, relIsExt,
   compareTo, isEqual;

synthesized attribute shortName::String;
synthesized attribute moduleName::QName;
synthesized attribute isQualified::Boolean;

--Put a new base name on the end (e.g. turn a:b:c into a:b:c:d)
inherited attribute addBase::String;
synthesized attribute baseAdded::QName;

--lookup as a nonterminal
synthesized attribute ntErrors::[Message];
synthesized attribute ntFound::Boolean;
synthesized attribute fullNT::QName;

--lookup as a production
synthesized attribute prodErrors::[Message];
synthesized attribute prodFound::Boolean;
synthesized attribute fullProd::QName;
synthesized attribute prodArgs::[Type];
synthesized attribute prodBuilds::QName;

--lookup the translation of the nonterminal
synthesized attribute transErrors::[Message];
synthesized attribute transFound::Boolean;
synthesized attribute fullTransNT::QName;
synthesized attribute transType::[Type];

--lookup as a relation
synthesized attribute relErrors::[Message];
synthesized attribute relFound::Boolean;
synthesized attribute fullRel::QName;
synthesized attribute relArgs::[Type];
synthesized attribute relIsExt::Boolean;


abstract production baseName
top::QName ::= name::String
{
  top.pp = name;

  top.isQualified = false;
  top.shortName = name;
  top.moduleName = error("Cannot access moduleName if unqualified");

  top.baseAdded = addModule(name, baseName(top.addBase));

  --lookup name as a nonterminal
  production attribute possibleNTs::[QName] =
     findNT(top, top.languageCtx);
  top.ntErrors =
      case possibleNTs of
      | [] -> [errorMsg("Unknown nonterminal " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate nonterminal " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp), possibleNTs)))]
      end;
  top.ntFound = length(possibleNTs) == 1;
  top.fullNT = head(possibleNTs);

  --lookup name as a production
  production attribute possibleProds::[(QName, [Type], QName)] =
     findProd(top, top.languageCtx);
  top.prodErrors =
      case possibleProds of
      | [] -> [errorMsg("Unknown production " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate production " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleProds))))]
      end;
  top.prodFound = length(possibleProds) == 1;
  top.fullProd = head(possibleProds).1;
  top.prodArgs = head(possibleProds).2;
  top.prodBuilds = head(possibleProds).3;

  --lookup name as a nonterminal to get translations
  production attribute possibleTrans::[(QName, [Type])] =
     findTrans(top, top.languageCtx);
  top.transErrors =
      case possibleTrans of
      | [] -> [errorMsg("Unknown translation nonterminal " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate translation nonterminal " ++
                  top.pp ++ "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleTrans))))]
      end;
  top.transFound = length(possibleTrans) == 1;
  top.fullTransNT = head(possibleTrans).1;
  top.transType = head(possibleTrans).2;

  --lookup name as a relation
  production attribute possibleRels::[(QName, [Type], Boolean)] =
     findRel(top, top.languageCtx);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ top.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleRels))))]
      end;
  top.relFound = length(possibleRels) == 1;
  top.relArgs = head(possibleRels).2;
  top.relIsExt = head(possibleRels).3;

  propagate compareTo, isEqual;
}


abstract production addModule
top::QName ::= name::String rest::QName
{
  top.pp = name ++ ":" ++ rest.pp;

  rest.languageCtx = top.languageCtx;

  top.isQualified = true;
  top.shortName = rest.shortName;
  top.moduleName = case rest of
                   | baseName(_) -> baseName(name)
                   | _ -> addModule(name, rest.moduleName)
                   end;

  rest.addBase = top.addBase;
  top.baseAdded = addModule(name, rest.baseAdded);

  --lookup name as a nonterminal
  production attribute possibleNTs::[QName] =
     findNT(top, top.languageCtx);
  top.ntErrors =
      case possibleNTs of
      | [] -> [errorMsg("Unknown nonterminal " ++ top.pp)]
      | [_] -> []
      | l -> --should be 0 or 1, but catch in case
        [errorMsg("Indeterminate nonterminal " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp), possibleNTs)))]
      end;
  top.ntFound = length(possibleNTs) == 1;
  top.fullNT = head(possibleNTs);

  --lookup name as a production
  production attribute possibleProds::[(QName, [Type], QName)] =
     findProd(top, top.languageCtx);
  top.prodErrors =
      case possibleProds of
      | [] -> [errorMsg("Unknown production " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate production " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleProds))))]
      end;
  top.prodFound = length(possibleProds) == 1;
  top.fullProd = head(possibleProds).1;
  top.prodArgs = head(possibleProds).2;
  top.prodBuilds = head(possibleProds).3;

  --lookup name as a nonterminal to get translations
  production attribute possibleTrans::[(QName, [Type])] =
     findTrans(top, top.languageCtx);
  top.transErrors =
      case possibleTrans of
      | [] -> [errorMsg("Unknown translation nonterminal " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate translation nonterminal " ++
                  top.pp ++ "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleTrans))))]
      end;
  top.transFound = length(possibleTrans) == 1;
  top.fullTransNT = head(possibleTrans).1;
  top.transType = head(possibleTrans).2;

  --lookup name as a relation
  production attribute possibleRels::[(QName, [Type], Boolean)] =
     findRel(top, top.languageCtx);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ top.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp), map(fst, possibleRels))))]
      end;
  top.relFound = length(possibleRels) == 1;
  top.relArgs = head(possibleRels).2;
  top.relIsExt = head(possibleRels).3;

  propagate compareTo, isEqual;
}





function toQName
QName ::= name::String
{
  return
     foldrLastElem(addModule(_, _), baseName(_), explode(":", name));
}


function addQNameBase
QName ::= module::QName name::String
{
  module.addBase = name;
  return module.baseAdded;
}
