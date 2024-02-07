grammar extensibella:toAbella:abstractSyntax;


nonterminal AnyCommand with
   pp, abella_pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   newProofState,
   priorStep, newPriorStep, newProverState,
   isQuit, interactive,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
      proverState, boundNames, toAbellaMsgs, interactive, priorStep
   on AnyCommand;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;
  top.abella_pp = c.abella_pp;

  top.toAbella = c.toAbella;

  top.toAbellaMsgs <-
      if top.proverState.state.inProof
      then [errorMsg("Cannot use top-level commands while in proof")]
      else [];

  c.newProofState = top.newProofState;

  top.newProverState =
      updateProverStateTop(top.proverState, top.newProofState,
         c.newTheorems, c.tys, c.rels, c.constrs, c.provingTheorems,
         c.provingExtInds, c.duringCommands, c.keyRelModules,
         c.afterCommands);
  top.newPriorStep = nothing();

  top.isQuit = false;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;
  top.abella_pp = c.abella_pp;

  top.toAbella = map(anyProofCommand, c.toAbella);

  top.newProverState =
      if c.isUndo
      then c.newProverState
      else setProofState(top.proverState, top.newProofState);
  top.newPriorStep =
      if c.isUndo
      then c.newPriorStep
      else nothing();

  top.toAbellaMsgs <-
      if top.proverState.state.inProof
      then []
      else [errorMsg("Cannot use proof commands when not in proof")];

  top.isQuit = false;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;
  top.abella_pp = c.abella_pp;

  top.toAbella = map(anyNoOpCommand, c.toAbella);

  top.newProverState = c.newProverState;
  top.newPriorStep = c.newPriorStep;

  top.isQuit = c.isQuit;
}


--Putting this in a production simplifies the run_step function
abstract production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.pp = text(parseErrors);
  top.abella_pp =
      error("anyParseFailure.abella_pp should not be accessed");

  top.toAbella = [];

  top.newProverState = top.proverState;
  top.newPriorStep = just(top.priorStep);

  top.toAbellaMsgs <- [errorMsg(parseErrors)];

  top.isQuit = false;
}
