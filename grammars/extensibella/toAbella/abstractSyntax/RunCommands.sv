grammar extensibella:toAbella:abstractSyntax;

import silver:util:subprocess;
import silver:util:cmdargs;

----------------------------------------------------------------------
--We need this here to get config for RunCommands and MWDA:

--We will use the parsed command line arguments as a way to pass along
--information about how things ought to run, so we give it a name:
type Configuration = Decorated CmdArgs;


--We pass along the Configuration so it can be used further down
inherited attribute config::Configuration;


attribute
   config
occurs on ListOfCommands, AnyCommand;

aspect production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  a.config = top.config;
  rest.config = top.config;
}
----------------------------------------------------------------------
--Same:

nonterminal SetOfParsers;

type AllParsers = Decorated SetOfParsers with {};
----------------------------------------------------------------------



{-
  Conceptually, RunCommands is introduced by extensibella:main:run.
  However, we need the nonterminal here to make undo and #back work,
  since we need priorStep to make their translations and determine
  their errors.  Thus we introduce it here in as minimal a manner as
  possible, leaving the true definition to its actual location.
-}

type PriorStep = Decorated RunCommands;

nonterminal RunCommands with
   isNull, priorStep, interactive, currentModule, proverState,
   numAbellaCommands, abella, ioin, parsers, config;

inherited attribute priorStep::PriorStep;
inherited attribute abella::ProcessHandle;
inherited attribute ioin::IOToken;
inherited attribute parsers::AllParsers;

synthesized attribute isNull::Boolean;

--number of Abella commands run by this step in the end
synthesized attribute numAbellaCommands::Integer;
flowtype numAbellaCommands {
   currentModule, interactive, priorStep, proverState, abella, ioin,
   config, parsers
} on RunCommands;

abstract production emptyRunCommands
top::RunCommands ::=
{
  top.isNull = true;
  top.numAbellaCommands = 0;
}




--just(_)   -> use the one in the just
--nothing() -> use this step we are in now
synthesized attribute newPriorStep::Maybe<PriorStep>;
synthesized attribute newProverState::ProverState;


--undo n Extensibella commands
function undoN
--just(num Abella commands, last step before undone stuff,
--     state after undoing)
--nothing():  can't go back that far
Maybe<(Integer, PriorStep, ProverState)> ::= n::Integer p::PriorStep
{
  return
      case n of
      | 1 ->
        if p.isNull
        then just((0, p, p.proverState)) --retract whole file
        else just((p.numAbellaCommands, p.priorStep, p.proverState))
      | _ when n <= 0 ->
        error("Cannot undo <= 0 (" ++ toString(n) ++ ")")
      | _ ->
        if p.isNull
        then nothing()
        else case undoN(n - 1, p.priorStep) of
             | nothing() -> nothing()
             | just((i, prior, prover)) ->
               just((i + p.numAbellaCommands, prior, prover))
             end
      end;
}
