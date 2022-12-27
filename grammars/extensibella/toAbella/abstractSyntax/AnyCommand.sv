grammar extensibella:toAbella:abstractSyntax;


nonterminal AnyCommand with
   pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   stateListIn, stateListOut,
   newProofState,
   isQuit,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, toAbellaMsgs on AnyCommand;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.toAbella = c.toAbella;

  top.toAbellaMsgs <-
      if top.proverState.state.inProof
      then [errorMsg("Cannot use top-level commands while in proof")]
      else [];

  c.newProofState = top.newProofState;

  top.stateListOut =
      (length(c.toAbella),
       proverState(c.builtNewProofState,
          top.proverState.debug,
          top.proverState.knownTheorems,
          top.proverState.remainingObligations,
          c.provingTheorems,
          c.duringCommands,
          c.afterCommands))::top.stateListIn;

  top.isQuit = false;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;

  top.toAbella = map(anyProofCommand, c.toAbella);

  top.toAbellaMsgs <-
      if top.proverState.state.inProof
      then []
      else [errorMsg("Cannot use proof commands when not in proof")];

  local currentState::ProverState = top.proverState;
  currentState.replaceState = top.newProofState;
  top.stateListOut =
      if c.isUndo
      then c.stateListOut
      else (length(c.toAbella),
            currentState.replacedState)::top.stateListIn;

  top.isQuit = false;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;

  top.toAbella =
      case c.toAbella of
      | nothing() -> []
      | just(n) -> [anyNoOpCommand(n)]
      end;

  c.stateListIn = top.stateListIn;
  top.stateListOut = c.stateListOut;

  top.isQuit = c.isQuit;
}


--Putting this in a production simplifies the run_step function
abstract production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.pp = parseErrors;

  top.toAbella = [];

  top.toAbellaMsgs <- [errorMsg(parseErrors)];

  --sholudn't be needed since this is an error
  top.stateListOut = top.stateListIn;

  top.isQuit = false;
}
