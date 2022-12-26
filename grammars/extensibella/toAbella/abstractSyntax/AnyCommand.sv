grammar extensibella:toAbella:abstractSyntax;


nonterminal AnyCommand with
   pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   stateListIn, stateListOut,
   newProofState,
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
          c.provingTheorems,
          top.proverState.debug,
          top.proverState.knownTheorems,
          top.proverState.remainingObligations))::top.stateListIn;
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

  local currentState::ProverState = head(top.stateListIn).snd;
  currentState.replaceState = newProofState;
  local newProofState::ProofState =
      case top.proverState.state of
      | extensible_proofInProgress(_, oMt, numProds) ->
        extensible_proofInProgress(top.newProofState, oMt, numProds)
      | _ -> top.newProofState
      end;
  top.stateListOut =
      if c.isUndo
      then c.stateListOut
      else (length(c.toAbella),
            currentState.replacedState)::top.stateListIn;
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
}
