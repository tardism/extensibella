grammar extensibella:fromAbella:abstractSyntax;


nonterminal FullDisplay with
   pp,
   fromAbella<FullDisplay>,
   typeEnv, relationEnv, constructorEnv,
   proof, isError, isWarning, proofEnded;
propagate typeEnv, relationEnv, constructorEnv on FullDisplay;

abstract production fullDisplay
top::FullDisplay ::= msg::ExtraInformation state::ProofState
{
  top.pp = msg.pp ++ (if msg.pp != "" then "\n\n" else "") ++ state.pp;

  top.fromAbella = fullDisplay(msg.fromAbella, state.fromAbella);

  top.proof = state;
  top.isError = msg.isError;
  top.isWarning = msg.isWarning;
  top.proofEnded =
      case state of
      | noProof() -> false
      | proofCompleted() -> true
      | proofAborted() -> true
      | proofInProgress(_, _, _) -> false
      end;
}


abstract production showDisplay
top::FullDisplay ::= tl::TheoremList
{
  top.pp = tl.pp;

  top.fromAbella = showDisplay(tl.fromAbella);

  --We don't know what the current state is
  top.proof = noProof();
  top.isError = false;
  top.isWarning = false;
  top.proofEnded = false;
}





nonterminal TheoremList with
   pp,
   fromAbella<TheoremList>,
   typeEnv, relationEnv, constructorEnv;
propagate typeEnv, relationEnv, constructorEnv on TheoremList;

abstract production theoremListEmpty
top::TheoremList ::=
{
  top.pp = "";

  top.fromAbella = theoremListEmpty();
}

abstract production theoremListAdd
top::TheoremList ::= name::QName body::Metaterm rest::TheoremList
{
  top.pp = "Theorem " ++ name.pp ++ " : " ++ body.pp ++ ".\n\n" ++ rest.pp;

  top.fromAbella =
      theoremListAdd(name.fromAbella, body.fromAbella, rest.fromAbella);
}





nonterminal ExtraInformation with
   pp,
   fromAbella<ExtraInformation>,
   typeEnv, relationEnv, constructorEnv,
   isError, isWarning;
propagate typeEnv, relationEnv, constructorEnv on ExtraInformation;


abstract production emptyInformation
top::ExtraInformation ::=
{
  top.pp = "";

  top.fromAbella = emptyInformation();

  top.isError = false;
  top.isWarning = false;
}


abstract production importInformation
top::ExtraInformation ::= moduleName::String
{
  top.pp = "Importing from \"" ++ moduleName ++ "\".";

  top.fromAbella = importInformation(moduleName);

  top.isError = false;
  top.isWarning = false;
}


abstract production syntaxErrorInformation
top::ExtraInformation ::=
{
  top.pp = "Syntax error.";

  top.fromAbella = syntaxErrorInformation();

  top.isError = true;
  top.isWarning = false;
}


abstract production processingError
top::ExtraInformation ::= msg::ProcessingErrorMessage
{
  top.pp = "Error: " ++ msg.pp;

  top.fromAbella = processingError(msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
}


abstract production typingError
top::ExtraInformation ::= msg::TypingErrorMessage
{
  top.pp = "Typing Error.\n" ++ msg.pp;

  top.fromAbella = typingError(msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
}


abstract production warningInformation
top::ExtraInformation ::= msg::WarningMessage
{
  top.pp = "Warning: " ++ msg.pp;

  top.fromAbella = warningInformation(msg.fromAbella);

  top.isError = false;
  top.isWarning = true;
}


abstract production alreadyImported
top::ExtraInformation ::= filepath::String
{
  top.pp = "Ignoring import: " ++ filepath ++
           " has already been imported.";

  top.fromAbella = alreadyImported(filepath);

  top.isError = false;
  top.isWarning = true;
}


abstract production importError
top::ExtraInformation ::= moduleName::String
                          msg::ProcessingErrorMessage
{
  top.pp = "Importing from \"" ++ moduleName ++
           "\".\nError: " ++ msg.pp;

  top.fromAbella = importError(moduleName, msg.fromAbella);

  top.isError = true;
  top.isWarning = false;
}

