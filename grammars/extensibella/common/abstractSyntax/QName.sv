grammar extensibella:common:abstractSyntax;

nonterminal QName with
   pp,
   typeEnv, constructorEnv, relationEnv,
   shortName, moduleName, isQualified,
   addBase, baseAdded,
   typeErrors, typeFound, fullType,
   constrErrors, constrFound, fullConstr,
   relErrors, relFound, fullRel,
   compareTo, isEqual;
propagate typeEnv, constructorEnv, relationEnv on QName;

synthesized attribute shortName::String;
synthesized attribute moduleName::QName;
synthesized attribute isQualified::Boolean;

--Put a new base name on the end (e.g. turn a:b:c into a:b:c:d)
inherited attribute addBase::String;
synthesized attribute baseAdded::QName;

--lookup as a type
synthesized attribute typeErrors::[Message];
synthesized attribute typeFound::Boolean;
synthesized attribute fullType::TypeEnvItem;

--lookup as a constructor
synthesized attribute constrErrors::[Message];
synthesized attribute constrFound::Boolean;
synthesized attribute fullConstr::ConstructorEnvItem;

--lookup as a relation
synthesized attribute relErrors::[Message];
synthesized attribute relFound::Boolean;
synthesized attribute fullRel::RelationEnvItem;


abstract production baseName
top::QName ::= name::String
{
  top.pp = name;

  top.isQualified = false;
  top.shortName = name;
  top.moduleName = error("Cannot access moduleName if unqualified");

  top.baseAdded = addModule(name, baseName(top.addBase));

  --lookup name as a nonterminal
  production attribute possibleTys::[TypeEnvItem] =
     lookupEnv(top, top.typeEnv);
  top.typeErrors =
      case possibleTys of
      | [] -> [errorMsg("Unknown type " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate type " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleTys))))]
      end;
  top.typeFound = length(possibleTys) == 1;
  top.fullType = head(possibleTys);

  --lookup name as a constructor
  production attribute possibleConstrs::[ConstructorEnvItem] =
     lookupEnv(top, top.constructorEnv);
  top.constrErrors =
      case possibleConstrs of
      | [] -> [errorMsg("Unknown constructor " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate constructor " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleConstrs))))]
      end;
  top.constrFound = length(possibleConstrs) == 1;
  top.fullConstr = head(possibleConstrs).1;

  --lookup name as a relation
  production attribute possibleRels::[RelationEnvItem] =
     lookupEnv(top, top.relationEnv);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ top.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleRels))))]
      end;
  top.relFound = length(possibleRels) == 1;

  propagate compareTo, isEqual;
}


abstract production addModule
top::QName ::= name::String rest::QName
{
  top.pp = name ++ ":" ++ rest.pp;

  top.isQualified = true;
  top.shortName = rest.shortName;
  top.moduleName = case rest of
                   | baseName(_) -> baseName(name)
                   | _ -> addModule(name, rest.moduleName)
                   end;

  rest.addBase = top.addBase;
  top.baseAdded = addModule(name, rest.baseAdded);

  --lookup name as a nonterminal
  production attribute possibleTys::[TypeEnvItem] =
     lookupEnv(top, top.typeEnv);
  top.typeErrors =
      case possibleTys of
      | [] -> [errorMsg("Unknown type " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate type " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleTys))))]
      end;
  top.typeFound = length(possibleTys) == 1;
  top.fullType = head(possibleTys);

  --lookup name as a constructor
  production attribute possibleConstrs::[ConstructorEnvItem] =
     lookupEnv(top, top.constructorEnv);
  top.constrErrors =
      case possibleConstrs of
      | [] -> [errorMsg("Unknown constructor " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate constructor " ++ top.pp ++ "; " ++
                  "possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleConstrs))))]
      end;
  top.constrFound = length(possibleConstrs) == 1;
  top.fullConstr = head(possibleConstrs).1;

  --lookup name as a relation
  production attribute possibleRels::[RelationEnvItem] =
     lookupEnv(top, top.relationEnv);
  top.relErrors =
      case possibleRels of
      | [] -> [errorMsg("Unknown relation " ++ top.pp)]
      | [_] -> []
      | l ->
        [errorMsg("Indeterminate relation " ++ top.pp ++
                  "; possibilities are " ++
                  implode(", ", map((.pp),
                                map((.name), possibleRels))))]
      end;
  top.relFound = length(possibleRels) == 1;

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
