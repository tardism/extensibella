grammar extensibella:fromAbella:abstractSyntax;


nonterminal FullDisplay with
   pp,
   proof, isError, isWarning, proofEnded;

abstract production fullDisplay
top::FullDisplay ::= msg::ExtraInformation state::ProofState
{
  top.pp = msg.pp ++ (if msg.pp != "" then "\n\n" else "") ++ state.pp;

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

  --We don't know what the current state is
  top.proof = noProof();
  top.isError = false;
  top.isWarning = false;
  top.proofEnded = false;
}





nonterminal TheoremList with
   pp;

abstract production theoremListEmpty
top::TheoremList ::=
{
  top.pp = "";
}

abstract production theoremListAdd
top::TheoremList ::= name::String body::Metaterm rest::TheoremList
{
  top.pp = "Theorem " ++ name ++ " : " ++ body.pp ++ ".\n\n" ++ rest.pp;
}





nonterminal ExtraInformation with
  pp,
  isError, isWarning;


abstract production emptyInformation
top::ExtraInformation ::=
{
  top.pp = "";

  top.isError = false;
  top.isWarning = false;
}


abstract production importInformation
top::ExtraInformation ::= moduleName::String
{
  top.pp = "Importing from \"" ++ moduleName ++ "\".";

  top.isError = false;
  top.isWarning = false;
}


abstract production syntaxErrorInformation
top::ExtraInformation ::=
{
  top.pp = "Syntax error.";

  top.isError = true;
  top.isWarning = false;
}


abstract production processingError
top::ExtraInformation ::= msg::ProcessingErrorMessage
{
  top.pp = "Error: " ++ msg.pp;

  top.isError = true;
  top.isWarning = false;
}


abstract production typingError
top::ExtraInformation ::= msg::TypingErrorMessage
{
  top.pp = "Typing Error.\n" ++ msg.pp;

  top.isError = true;
  top.isWarning = false;
}


abstract production warningInformation
top::ExtraInformation ::= msg::WarningMessage
{
  top.pp = "Warning: " ++ msg.pp;

  top.isError = false;
  top.isWarning = true;
}


abstract production alreadyImported
top::ExtraInformation ::= filepath::String
{
  top.pp = "Ignoring import: " ++ filepath ++ " has already been imported.";

  top.isError = false;
  top.isWarning = true;
}


abstract production importError
top::ExtraInformation ::= moduleName::String msg::ProcessingErrorMessage
{
  top.pp = "Importing from \"" ++ moduleName ++ "\".\nError: " ++ msg.pp;

  top.isError = true;
  top.isWarning = false;
}

