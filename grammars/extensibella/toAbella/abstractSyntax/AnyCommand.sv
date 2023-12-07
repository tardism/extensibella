grammar extensibella:toAbella:abstractSyntax;


nonterminal AnyCommand with
   pp, abella_pp,
   toAbella<[AnyCommand]>, toAbellaMsgs,
   stateListIn, stateListOut,
   newProofState,
   isQuit, interactive,
   boundNames,
   typeEnv, constructorEnv, relationEnv, currentModule, proverState;
propagate typeEnv, constructorEnv, relationEnv, currentModule,
          proverState, boundNames, toAbellaMsgs, interactive
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

  top.stateListOut =
      (length(c.toAbella),
       updateProverStateTop(top.proverState, top.newProofState,
          c.newTheorems, c.tys, c.rels, c.constrs, c.provingTheorems,
          c.provingExtInds, c.duringCommands, c.afterCommands)
      )::top.stateListIn;

  top.isQuit = false;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;
  top.abella_pp = c.abella_pp;

  top.toAbella = map(anyProofCommand, c.toAbella);

  top.toAbellaMsgs <-
      if top.proverState.state.inProof
      then []
      else [errorMsg("Cannot use proof commands when not in proof")];

  c.stateListIn = top.stateListIn;
  top.stateListOut =
      if c.isUndo
      then c.stateListOut
      else (length(c.toAbella),
            setProofState(top.proverState, top.newProofState)
           )::top.stateListIn;

  top.isQuit = false;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;
  top.abella_pp = c.abella_pp;

  top.toAbella = map(anyNoOpCommand, c.toAbella);

  c.stateListIn = top.stateListIn;
  top.stateListOut = c.stateListOut;

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

  top.toAbellaMsgs <- [errorMsg(parseErrors)];

  --shouldn't be needed since this is an error
  top.stateListOut = top.stateListIn;

  top.isQuit = false;
}
