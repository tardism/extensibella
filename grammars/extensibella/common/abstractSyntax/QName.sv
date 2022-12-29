grammar extensibella:common:abstractSyntax;

{-
  We split into QName and SubQName to handle prefixes that may or may
  not occur at the beginning of a given QName.
-}

nonterminal QName with baseAdded<QName>, moduleName<QName>;
nonterminal SubQName with baseAdded<SubQName>, moduleName<SubQName>;
attribute
   pp, abella_pp,
   typeEnv, constructorEnv, relationEnv,
   shortName, isQualified,
   boundNames,
   addBase,
   typeErrors, typeFound, fullType,
   constrErrors, constrFound, fullConstr,
   relErrors, relFound, fullRel,
   compareTo, isEqual
occurs on QName, SubQName;
propagate typeEnv, constructorEnv, relationEnv on QName, SubQName;

synthesized attribute shortName::String;
synthesized attribute moduleName<a>::a;
synthesized attribute isQualified::Boolean;

--Put a new base name on the end (e.g. turn a:b:c into a:b:c:d)
inherited attribute addBase::String;
synthesized attribute baseAdded<a>::a;

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

--for internal use
synthesized attribute sub::SubQName occurs on QName;


abstract production baseName
top::SubQName ::= name::String
{
  top.pp = name;
  top.abella_pp = name;

  top.isQualified = false;
  top.shortName = name;
  top.moduleName = error("Cannot access moduleName if unqualified");

  top.baseAdded = addModule(name, baseName(top.addBase));

  --lookup name as a nonterminal
  production attribute possibleTys::[TypeEnvItem] =
     lookupEnv(basicQName(top), top.typeEnv);
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
     lookupEnv(basicQName(top), top.constructorEnv);
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
     lookupEnv(basicQName(top), top.relationEnv);
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
  top.fullRel = head(possibleRels);

  propagate compareTo, isEqual;
}


abstract production addModule
top::SubQName ::= name::String rest::SubQName
{
  top.pp = name ++ ":" ++ rest.pp;
  top.abella_pp = name ++ name_sep ++ rest.abella_pp;

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
     lookupEnv(basicQName(top), top.typeEnv);
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
     lookupEnv(basicQName(top), top.constructorEnv);
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
     lookupEnv(basicQName(top), top.relationEnv);
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
  top.fullRel = head(possibleRels);

  propagate compareTo, isEqual;
}




{-
  We only check the SubQName for equality because the user never
  enters the prefix, and indeed cannot enter it.
-}
--fixed relations from a language
abstract production fixQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$fix__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = fixQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--extensible relations from a language
abstract production extQName
top::QName ::= pc::Integer rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$ext__" ++ toString(pc) ++ "__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = extQName(pc, rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--translation relations
abstract production transQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$trans__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = transQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--types defined in a language
abstract production tyQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$ty__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = tyQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--anything from the standard library
abstract production libQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = "$lib__" ++ rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = libQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}


--anything without a prefix
abstract production basicQName
top::QName ::= rest::SubQName
{
  top.pp = rest.pp;
  top.abella_pp = rest.abella_pp;

  top.isQualified = rest.isQualified;
  top.shortName = rest.shortName;
  top.moduleName = basicQName(rest.moduleName);

  rest.addBase = top.addBase;
  top.baseAdded = basicQName(rest.baseAdded);

  top.typeErrors = rest.typeErrors;
  top.typeFound = rest.typeFound;
  top.fullType = rest.fullType;

  top.constrErrors = rest.constrErrors;
  top.constrFound = rest.constrFound;
  top.fullConstr = rest.fullConstr;

  top.relErrors = rest.relErrors;
  top.relFound = rest.relFound;
  top.fullRel = rest.fullRel;

  top.sub = rest;

  rest.compareTo = decorate top.compareTo.sub with {};
  top.isEqual = rest.isEqual;
}





function addQNameBase
QName ::= module::QName name::String
{
  module.addBase = name;
  return module.baseAdded;
}


function toQName
QName ::= name::String
{
  --choose splitter based on whether it uses colons
  local splitter::String =
      if indexOf(":", name) >= 0 then ":" else name_sep;
  local buildSub::(SubQName ::= Integer String) =
      \ i::Integer name::String ->
        foldrLastElem(addModule, baseName,
           explode(splitter, substring(i, length(name), name)));
  return
      if startsWith("$fix__", name)
      then fixQName(buildSub(6, name))
      else if startsWith("$ext__", name)
      then let shortened::String = substring(6, length(name), name)
           in
           let stop::Integer = indexOf("__", shortened)
           in
           let pc::Integer = toInteger(substring(0, stop, shortened))
           in
             extQName(pc, buildSub(stop + 2, shortened))
           end end end
      else if startsWith("$trans__", name)
      then fixQName(buildSub(7, name))
      else if startsWith("$ty__", name)
      then tyQName(buildSub(5, name))
      else if startsWith("$lib__", name)
      then libQName(buildSub(6, name))
      else basicQName(buildSub(0, name));
}
