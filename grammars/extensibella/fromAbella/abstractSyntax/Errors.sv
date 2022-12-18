grammar extensibella:fromAbella:abstractSyntax;





nonterminal WarningMessage with
   pp;

abstract production stratificationWarning
top::WarningMessage ::= name::String
{
  top.pp = "Definition might not be stratified\n (\"" ++ name ++ "\" occurs to the left of ->)";
}


abstract production defeatStratification
top::WarningMessage ::= name::String
{
  top.pp = "Definition can be used to defeat stratification\n" ++
           " (higher-order argument \"" ++ name ++ "\" occurs to the left of ->)";
}


abstract production overridingLemma
top::WarningMessage ::= name::String
{
  top.pp = "overriding existing lemma named \"" ++ name ++ "\"";
}





nonterminal ProcessingErrorMessage with
   pp;

abstract production undeterminedVarType
top::ProcessingErrorMessage ::=
{
  top.pp = "Types of variables are not fully determined";
}


abstract production searchFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Search failed";
}


abstract production unknownHypLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Could not find hypothesis or lemma " ++ name;
}


abstract production unknownConstant
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown constant: " ++ name;
}


abstract production importedUnknownTy
top::ProcessingErrorMessage ::= names::[String]
{
  local namesString::String = implode(", ", names);
  top.pp = "Imported file makes reference to unknown types: " ++ namesString;
}


abstract production invalidFormula
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid formula: " ++ formula.pp ++
           "\nCannot use size restrictions (*, @, #, or +)";
}


abstract production unboundedTyVars
top::ProcessingErrorMessage ::=
{
  top.pp = "Some type variables in the theorem are not bounded";
}


abstract production alreadyDefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Predicate or constant " ++ name ++ " already exists";
}


abstract production invalidCapDefName
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Invalid defined predicate name \"" ++ name ++
           "\".\n Defined predicates may not begin with a capital letter.";
}


abstract production invalidCapConstName
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Constants may not begin with a capital letter: " ++ name;
}


abstract production strayClause
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Found stray clause for " ++ name;
}


abstract production invalidHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid head in definition: " ++ formula.pp;
}


abstract production nonatomicHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Definitional clause head not atomic:\n" ++ formula.pp;
}


abstract production caseUndefinedAtom
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot perform case-analysis on undefined atom";
}


abstract production unknownHypVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown hypothesis or variable " ++ name;
}


abstract production unknownTheorem
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Could not find theorem named \"" ++ name ++ "\"";
}


abstract production unknownVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable " ++ name;
}


abstract production inductPredJudg
top::ProcessingErrorMessage ::=
{
  top.pp = "Can only induct on predicates and judgments";
}


abstract production inductUndefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Cannot induct on " ++ name ++ " since it has not been defined";
}


abstract production tooManyInductions
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = "Expecting " ++ toString(expected) ++
           " induction arguments but got " ++ toString(got);
}


abstract production needlessSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Needless use of split";
}


abstract production cannotSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot split this type of theorem";
}


abstract production nameExistingHyp
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to an existing hypothesis";
}


abstract production nameExistingLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to a lemma";
}


abstract production nameExistingVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to an existing variable";
}


abstract production unknownVarHypLabel
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable or hypothesis label \"" ++ name ++ "\"";
}


abstract production cannotGoBack
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot go that far back!";
}


abstract production matchingUnificationFailureConstants
top::ProcessingErrorMessage ::= argnum::Integer const1::String const2::String
{
  top.pp = "While matching argument #" ++ toString(argnum) ++
           ":\nUnification failure (constant clash between " ++
           const1 ++ " and " ++ const2 ++ ")";
}


abstract production matchingUnificationFailure
top::ProcessingErrorMessage ::= argnum::Integer
{
  top.pp = "While matching argument #" ++ toString(argnum) ++
           ":\nUnification failure";
}


abstract production unificationFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Unification failure";
}


abstract production tyConstrInconsistentKinds
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Type constructor " ++ name ++ " has inconsistent kind declarations";
}


abstract production tyNoCaps
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Types may not begin with a capital letter: " ++ name;
}


abstract production unknownTyConstr
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown type constructor: " ++ name;
}


abstract production wrongArgNumber
top::ProcessingErrorMessage ::= name::String expected::Integer given::Integer
{
  top.pp = name ++ " expects " ++ toString(expected) ++ " arguments but has " ++ toString(given);
}


abstract production noQuantifyProp
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot quantify over type prop";
}


abstract production unknownSettingKey
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown key '" ++ name ++ "'";
}


abstract production unknownSettingsValueExpectInt
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected non-negative integer";
}


abstract production unknownSettingsValueExpectOnOff
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected 'on' or 'off'";
}


abstract production unknownSettingsValueExpectMany
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected 'on', 'off', non-negative integer, or depth specification";
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
}


abstract production logicVariableToplevel
top::ProcessingErrorMessage ::=
{
  top.pp = "Found logic variable at toplevel";
}


abstract production appliedStructure
top::ProcessingErrorMessage ::=
{
  top.pp =
      "Structure of applied term must be a substructure of the following.\n" ++
      "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C";
}





nonterminal TypingErrorMessage with
   pp;

abstract production badTypeUsage
top::TypingErrorMessage ::= hasType::Type usedType::Type
{
  top.pp = "Expression has type " ++ hasType.pp ++ " but is used here with type " ++ usedType.pp ++ ".";
}


abstract production tooManyArguments
top::TypingErrorMessage ::=
{
  top.pp = "Expression is applied to too many arguments";
}





--attribute occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{

}


aspect production nameType
top::Type ::= name::String
{

}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{

}


aspect production underscoreType
top::Type ::=
{

}

