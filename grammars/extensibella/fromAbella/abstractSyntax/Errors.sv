grammar extensibella:fromAbella:abstractSyntax;





nonterminal WarningMessage with
   pp,
   fromAbella<WarningMessage>;

abstract production stratificationWarning
top::WarningMessage ::= name::QName
{
  top.pp = "Definition might not be stratified\n (\"" ++ name.pp ++
           "\" occurs to the left of ->)";

  top.fromAbella = stratificationWarning(name);
}


abstract production defeatStratification
top::WarningMessage ::= name::QName
{
  top.pp = "Definition can be used to defeat stratification\n" ++
           " (higher-order argument \"" ++ name.pp ++
           "\" occurs to the left of ->)";

  top.fromAbella = defeatStratification(name);
}


abstract production overridingLemma
top::WarningMessage ::= name::QName
{
  top.pp = "overriding existing lemma named \"" ++ name.pp ++ "\"";

  top.fromAbella = overridingLemma(name);
}





nonterminal ProcessingErrorMessage with
   pp,
   fromAbella<ProcessingErrorMessage>,
   typeEnv, relationEnv, constructorEnv;
propagate typeEnv, relationEnv, constructorEnv
   on ProcessingErrorMessage;

abstract production undeterminedVarType
top::ProcessingErrorMessage ::=
{
  top.pp = "Types of variables are not fully determined";

  top.fromAbella = undeterminedVarType();
}


abstract production searchFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Search failed";

  top.fromAbella = searchFailure();
}


abstract production unknownHypLemma
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = "Could not find hypothesis or lemma " ++ name.pp;

  top.fromAbella = unknownHypLemma(name.fromAbella);
}


abstract production unknownConstant
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown constant: " ++ name;

  top.fromAbella = unknownConstant(name);
}


abstract production importedUnknownTy
top::ProcessingErrorMessage ::= names::[String]
{
  local namesString::String = implode(", ", names);
  top.pp = "Imported file makes reference to unknown types: " ++ namesString;

  top.fromAbella = importedUnknownTy(names);
}


abstract production invalidFormula
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid formula: " ++ formula.pp ++
           "\nCannot use size restrictions (*, @, #, or +)";

  top.fromAbella = invalidFormula(formula.fromAbella);
}


abstract production unboundedTyVars
top::ProcessingErrorMessage ::=
{
  top.pp = "Some type variables in the theorem are not bounded";

  top.fromAbella = unboundedTyVars();
}


abstract production alreadyDefined
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = "Predicate or constant " ++ name.pp ++ " already exists";

  top.fromAbella = alreadyDefined(name);
}


abstract production invalidCapDefName
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = "Invalid defined predicate name \"" ++ name.pp ++
           "\".\n Defined predicates may not begin with a " ++
           "capital letter.";

  top.fromAbella = invalidCapDefName(name);
}


abstract production invalidCapConstName
top::ProcessingErrorMessage ::= name::QName
{
  top.pp =
      "Constants may not begin with a capital letter: " ++ name.pp;

  top.fromAbella = invalidCapConstName(name);
}


abstract production strayClause
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Found stray clause for " ++ name;

  top.fromAbella = strayClause(name);
}


abstract production invalidHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid head in definition: " ++ formula.pp;

  top.fromAbella = invalidHead(formula.fromAbella);
}


abstract production nonatomicHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Definitional clause head not atomic:\n" ++ formula.pp;

  top.fromAbella = nonatomicHead(formula.fromAbella);
}


abstract production caseUndefinedAtom
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot perform case-analysis on undefined atom";

  top.fromAbella = caseUndefinedAtom();
}


abstract production unknownHypVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown hypothesis or variable " ++ name;

  top.fromAbella = unknownHypVar(name);
}


abstract production unknownTheorem
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Could not find theorem named \"" ++ name ++ "\"";

  top.fromAbella = unknownTheorem(name);
}


abstract production unknownVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable " ++ name;

  top.fromAbella = unknownVar(name);
}


abstract production inductPredJudg
top::ProcessingErrorMessage ::=
{
  top.pp = "Can only induct on predicates and judgments";

  top.fromAbella = inductPredJudg();
}


abstract production inductUndefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Cannot induct on " ++ name ++
           " since it has not been defined";

  top.fromAbella = inductUndefined(name);
}


abstract production tooManyInductions
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = "Expecting " ++ toString(expected) ++
           " induction arguments but got " ++ toString(got);

  top.fromAbella = tooManyInductions(expected, got);
}


abstract production needlessSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Needless use of split";

  top.fromAbella = needlessSplit();
}


abstract production cannotSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot split this type of theorem";

  top.fromAbella = cannotSplit();
}


abstract production nameExistingHyp
top::ProcessingErrorMessage ::= name::String
{
  top.pp =
      "\"" ++ name ++ "\" already refers to an existing hypothesis";

  top.fromAbella = nameExistingHyp(name);
}


abstract production nameExistingLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to a lemma";

  top.fromAbella = nameExistingLemma(name);
}


abstract production nameExistingVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to an existing variable";

  top.fromAbella = nameExistingVar(name);
}


abstract production unknownVarHypLabel
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable or hypothesis label \"" ++ name ++ "\"";

  top.fromAbella = unknownVarHypLabel(name);
}


abstract production cannotGoBack
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot go that far back!";

  top.fromAbella = cannotGoBack();
}


abstract production matchingUnificationFailureConstants
top::ProcessingErrorMessage ::= argnum::Integer const1::QName const2::QName
{
  top.pp = "While matching argument #" ++ toString(argnum) ++
           ":\nUnification failure (constant clash between " ++
           const1.pp ++ " and " ++ const2.pp ++ ")";

  top.fromAbella =
      matchingUnificationFailureConstants(argnum, const1, const2);
}


abstract production matchingUnificationFailure
top::ProcessingErrorMessage ::= argnum::Integer
{
  top.pp = "While matching argument #" ++ toString(argnum) ++
           ":\nUnification failure";

  top.fromAbella = matchingUnificationFailure(argnum);
}


abstract production unificationFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Unification failure";

  top.fromAbella = unificationFailure();
}


abstract production tyConstrInconsistentKinds
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = "Type constructor " ++ name.pp ++
           " has inconsistent kind declarations";

  top.fromAbella = tyConstrInconsistentKinds(name);
}


abstract production tyNoCaps
top::ProcessingErrorMessage ::= name::QName
{
  top.pp = "Types may not begin with a capital letter: " ++ name.pp;

  top.fromAbella = tyNoCaps(name);
}


abstract production unknownTyConstr
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown type constructor: " ++ name;

  top.fromAbella = unknownTyConstr(name);
}


abstract production wrongArgNumber
top::ProcessingErrorMessage ::= name::QName expected::Integer
                                given::Integer
{
  top.pp = name.pp ++ " expects " ++ toString(expected) ++
           " arguments but has " ++ toString(given);

  top.fromAbella = wrongArgNumber(name, expected, given);
}


abstract production noQuantifyProp
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot quantify over type prop";

  top.fromAbella = noQuantifyProp();
}


abstract production unknownSettingKey
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown key '" ++ name ++ "'";

  top.fromAbella = unknownSettingKey(name);
}


abstract production unknownSettingsValueExpectInt
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++
           "\"; expected non-negative integer";

  top.fromAbella = unknownSettingsValueExpectInt(val, key);
}


abstract production unknownSettingsValueExpectOnOff
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++
           "\"; expected 'on' or 'off'";

  top.fromAbella = unknownSettingsValueExpectOnOff(val, key);
}


abstract production unknownSettingsValueExpectMany
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++
           "\"; expected 'on', 'off', non-negative integer, or " ++
           "depth specification";

  top.fromAbella = unknownSettingsValueExpectMany(val, key);
}


abstract production applyWrongArgsNumber
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp =
      ( if expected > got
        then "Not enough"
        else "Too many" ) ++
      " arguments to apply\n(Expected " ++ toString(expected) ++
      " but got " ++ toString(got) ++ ")";

  top.fromAbella = applyWrongArgsNumber(expected, got);
}


abstract production logicVariableToplevel
top::ProcessingErrorMessage ::=
{
  top.pp = "Found logic variable at toplevel";

  top.fromAbella = logicVariableToplevel();
}


abstract production appliedStructure
top::ProcessingErrorMessage ::=
{
  top.pp =
      "Structure of applied term must be a substructure of the following.\n" ++
      "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C";

  top.fromAbella = appliedStructure();
}


abstract production inductiveRestrictionViolated
top::ProcessingErrorMessage ::=
{
  top.pp = "Inductive restriction violated";

  top.fromAbella = inductiveRestrictionViolated();
}





nonterminal TypingErrorMessage with
   pp,
   fromAbella<TypingErrorMessage>,
   typeEnv;
propagate typeEnv on TypingErrorMessage;

abstract production badTypeUsage
top::TypingErrorMessage ::= hasType::Type usedType::Type
{
  top.pp = "Expression has type " ++ hasType.pp ++
           " but is used here with type " ++ usedType.pp ++ ".";

  top.fromAbella =
      badTypeUsage(hasType.fromAbella, usedType.fromAbella);
}


abstract production tooManyArguments
top::TypingErrorMessage ::=
{
  top.pp = "Expression is applied to too many arguments";

  top.fromAbella = tooManyArguments();
}





attribute
   fromAbella<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.fromAbella = arrowType(ty1.fromAbella, ty2.fromAbella);
}


aspect production nameType
top::Type ::= name::QName
{
  top.fromAbella = nameType(name.tyFromAbella);
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.fromAbella =
      case functorTy, argTy of
      | nameType(basicQName(baseName("list"))),
        nameType(basicQName(baseName("$char"))) ->
        nameType(toQName("string"))
      | _, _ ->
        functorType(functorTy.fromAbella, argTy.fromAbella)
      end;
}


aspect production varType
top::Type ::= name::String
{
  top.fromAbella = top;
}


aspect production errorType
top::Type ::=
{
  top.fromAbella = error("errorType.fromAbella");
}





attribute
   fromAbella<MaybeType>
occurs on MaybeType;

aspect production nothingType
top::MaybeType ::=
{
  top.fromAbella = nothingType();
}


aspect production justType
top::MaybeType ::= ty::Type
{
  top.fromAbella = justType(ty.fromAbella);
}
