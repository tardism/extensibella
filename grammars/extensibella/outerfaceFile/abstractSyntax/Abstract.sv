grammar extensibella:outerfaceFile:abstractSyntax;

imports extensibella:common:abstractSyntax;
imports extensibella:toAbella:abstractSyntax;



function processModuleOuterfaces
([DefElement], [ThmElement]) ::= mods::[(QName, Outerface)]
{
  local allDefs::[DefElement] =
      flatMap((.defElements), map(snd, mods));
  local allThms::[(QName, [ThmElement])] =
      map(\ p::(QName, Outerface) -> (p.1, p.2.thmElements),
          mods);
  local sortedThms::[(QName, [ThmElement])] =
      sortBy(\ p1::(QName, [ThmElement]) p2::(QName, [ThmElement]) ->
               p1.1.pp < p2.1.pp, allThms);
  local justThms::[[ThmElement]] = map(snd, sortedThms);
  local finalThms::[ThmElement] = combineAllThms(justThms);
  return (allDefs, finalThms);
}



function combineAllThms
[ThmElement] ::= modThms::[[ThmElement]]
{
  local firsts::[ThmElement] = map(head, modThms);
  local first::ThmElement = getFirst(tail(firsts), head(firsts));
  local cleaned::[[ThmElement]] = cleanModThms(first, modThms);
  return
     case modThms of
     | [] -> []
     | [l] -> l
     | _ -> first::combineAllThms(cleaned)
     end;
}


function getFirst
ThmElement ::= modThms::[ThmElement] thusFar::ThmElement
{
  return
     case modThms, thusFar of
     | [], x -> x
     --if both extensible, combine them if they contain shared
     --theorems, otherwise take the earlier one
     | extensibleMutualTheoremGroup(thms1)::rest,
       extensibleMutualTheoremGroup(thms2) ->
       if null(intersect(map(fst, thms1), map(fst, thms2)))
       then getFirst(rest, thusFar)
       else getFirst(rest,
               extensibleMutualTheoremGroup(
                  unionBy(\ p1::(QName, Bindings, ExtBody, String)
                            p2::(QName, Bindings, ExtBody, String) ->
                            p1.1 == p2.1,
                          thms1, thms2)))
     --if one is not extensible, just take it
     | x::rest, extensibleMutualTheoremGroup(_) -> x
     | _::rest, x -> x
     end;
}


function cleanModThms
[[ThmElement]] ::= remove::ThmElement modThms::[[ThmElement]]
{
  --whether to remove the first thing in the first list
  local removeFirst::Boolean =
      case head(head(modThms)), remove of
      | splitElement(aname, alst), splitElement(bname, blst) ->
        aname == bname && alst == blst
      | nonextensibleTheorem(aname, aparams, astmt),
        nonextensibleTheorem(bname, bparams, bstmt) ->
        aname == bname
      | extensibleMutualTheoremGroup(athms),
        extensibleMutualTheoremGroup(bthms) ->
        !null(intersect(map(fst, athms), map(fst, bthms)))
      | translationConstraintTheorem(aname, abinds, abody),
        translationConstraintTheorem(bname, bbinds, bbody) ->
        aname == bname
      | extIndElement(arel, _, _, _, _, _, _),
        extIndElement(brel, _, _, _, _, _, _) ->
        arel == brel
      | _, _ -> false
      end;
  return case modThms of
         | [] -> []
         | [_]::tl when removeFirst ->
           cleanModThms(remove, tl)
         | (_::rest)::tl when removeFirst ->
           rest::cleanModThms(remove, tl)
         | hd::tl -> --!removeFirst
           hd::cleanModThms(remove, tl)
         end;
}



synthesized attribute defElements::[DefElement];
synthesized attribute thmElements::[ThmElement];

nonterminal Outerface with pp, len, defElements, thmElements;

abstract production outerface
top::Outerface ::= t::TopCommands
{
  top.pp = t.pp;
  top.len = t.len;

  top.defElements = t.defElements;
  top.thmElements = t.thmElements;
}





nonterminal TopCommands with pp, len, defElements, thmElements;

abstract production endTopCommands
top::TopCommands ::=
{
  top.pp = "";
  top.len = 0;

  top.defElements = [];
  top.thmElements = [];
}


abstract production addTopCommands
top::TopCommands ::= t::TopCommand rest::TopCommands
{
  top.pp = t.pp ++ rest.pp;
  top.len = 1 + rest.len;

  top.defElements = t.defElements ++ rest.defElements;
  top.thmElements = t.thmElements ++ rest.thmElements;
}





attribute
   defElements, thmElements
occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::QName params::[String] body::Metaterm
{
  top.defElements = [];
  top.thmElements = [nonextensibleTheorem(name, params, body)];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.defElements = [defineElement(preds, defs.defClauses)];
  top.thmElements = [];
}


aspect production codefinitionDeclaration
top::TopCommand ::= preds::[(QName, Type)] defs::Defs
{
  top.defElements = [codefineElement(preds, defs.defClauses)];
  top.thmElements = [];
}


aspect production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.defElements =
      error("Should not have query command in interface file");
  top.thmElements =
      error("Should not have query command in interface file");
}


aspect production splitTheorem
top::TopCommand ::= theoremName::QName newTheoremNames::[QName]
{
  top.defElements = [];
  top.thmElements = [splitElement(theoremName, newTheoremNames)];
}


aspect production closeCommand
top::TopCommand ::= tys::TypeList
{
  top.defElements = [];
  top.thmElements = [];
}


aspect production kindDeclaration
top::TopCommand ::= names::[QName] k::Kind
{
  top.defElements = [kindElement(names, k)];
  top.thmElements = [];
}


aspect production typeDeclaration
top::TopCommand ::= names::[QName] ty::Type
{
  top.defElements = [typeElement(names, ty)];
  top.thmElements = [];
}


aspect production importCommand
top::TopCommand ::= name::String
{
  top.defElements = [];
  top.thmElements = [];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= thms::ExtThms
{
  top.defElements = [];
  top.thmElements = [extensibleMutualTheoremGroup(thms.thmInfo)];
}


aspect production proveObligations
top::TopCommand ::= names::[QName]
{
  top.defElements =
      error("Should not have proveObligations in interface file");
  top.thmElements =
      error("Should not have proveObligations in interface file");
}


aspect production translationConstraint
top::TopCommand ::= name::QName binds::Bindings body::ExtBody
{
  top.defElements = [];
  top.thmElements = [translationConstraintTheorem(name, binds, body)];
}


aspect production proveConstraint
top::TopCommand ::= name::QName
{
  top.defElements =
      error("Should not have proveConstraint in interface file");
  top.thmElements =
      error("Should not have proveConstraint in interface file");
}


aspect production extIndDeclaration
top::TopCommand ::= rel::QName relArgs::[String]
                    boundVars::MaybeBindings transArgs::TermList
                    transTy::QName original::String translated::String
{
  top.defElements = [];
  top.thmElements = [extIndElement(rel, relArgs, boundVars.usedNames,
                        transArgs, transTy, original, translated)];
}


aspect production proveExtInd
top::TopCommand ::= rel::QName
{
  top.defElements =
      error("Should not have proveExtInd in interface file");
  top.thmElements =
      error("Should not have proveExtInd in interface file");
}





attribute
   thmInfo
occurs on ExtThms;

synthesized attribute thmInfo::[(QName, Bindings, ExtBody, String)];

aspect production endExtThms
top::ExtThms ::=
{
  top.thmInfo = [];
}


aspect production addExtThms
top::ExtThms ::= name::QName bindings::Bindings body::ExtBody
                 onLabel::String rest::ExtThms
{
  top.thmInfo = (name, bindings, body, onLabel)::rest.thmInfo;
}





attribute
   defClauses
occurs on Defs, Def;

synthesized attribute defClauses::[(QName, TermList, Maybe<Metaterm>)];

aspect production singleDefs
top::Defs ::= d::Def
{
  top.defClauses = d.defClauses;
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.defClauses = d.defClauses ++ rest.defClauses;
}



aspect production factDef
top::Def ::= q::QName args::TermList
{
  top.defClauses = [(q, args, nothing())];
}


aspect production ruleDef
top::Def ::= q::QName args::TermList body::Metaterm
{
  top.defClauses = [(q, args, just(body))];
}
