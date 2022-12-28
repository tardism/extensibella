grammar extensibella:fromAbella:abstractSyntax;

attribute
   fromAbella<QName>, relFromAbella, tyFromAbella, constrFromAbella,
   isTranslation, transFromAbella
occurs on QName;

synthesized attribute isTranslation::Boolean;

synthesized attribute transFromAbella::QName;
synthesized attribute relFromAbella::QName;
synthesized attribute tyFromAbella::QName;
synthesized attribute constrFromAbella::QName;

aspect production baseName
top::QName ::= name::String
{
  --if we only have the short name, this is a var
  top.fromAbella = baseName(name);

  top.isTranslation = false;
  top.transFromAbella = error("Not possible");

  top.relFromAbella = top;
  top.tyFromAbella = top;
  top.constrFromAbella = top;
}


aspect production addModule
top::QName ::= name::String rest::QName
{
  top.isTranslation = startsWith("$trans__", name);
  top.transFromAbella =
      case lookupEnv(baseName(rest.shortName), top.typeEnv) of
      | [] -> error("Not possible")
      | [_] -> baseName(rest.shortName) --no confusion
      | l ->  --drop $trans__ from type name
        addModule(substring(7, length(name), name), rest)
      end;

  --fromAbella should only be for error messages from QName, so use
  --the full name
  top.fromAbella = top;

  --check if there are other relations by the same short name
  --only translates 
  top.relFromAbella =
      case lookupEnv(baseName(rest.shortName), top.relationEnv) of
      | [] -> error("Not possible")
      | [_] -> baseName(rest.shortName) --no confusion
      | l -> top
      end;

  --check if there are other types by the same short name
  top.tyFromAbella =
      case lookupEnv(baseName(rest.shortName), top.typeEnv) of
      | [] -> error("Not possible")
      | [_] -> baseName(rest.shortName) --no confusion
      | l -> top
      end;

  --check if there are other constructors by the same short name
  top.constrFromAbella =
      case lookupEnv(baseName(rest.shortName), top.constructorEnv) of
      | [] -> error("Not possible")
      | [_] -> baseName(rest.shortName) --no confusion
      | l -> top
      end;
}
