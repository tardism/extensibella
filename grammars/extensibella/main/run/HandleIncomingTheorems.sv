grammar extensibella:main:run;


function handleIncomingThms
--(commands for filling in anything imported,
-- updated prover state without the obligations we handled)
([AnyCommand], ProverState) ::= initialState::ProverState
{
  local obligations::[ThmElement] = initialState.remainingObligations;
  --
  local doThms::[ThmElement] =
        takeWhile((.is_nonextensible), obligations);
  local initialCommands::[AnyCommand] =
        flatMap(\ t::ThmElement -> t.encode, doThms);
  local commands::[AnyCommand] =
      flatMap(\ c::AnyCommand ->
                decorate c with {
                   currentModule = error("currentModule not needed");
                   priorStep = error("priorStep not needed");
                   proverState = initialState;
                   typeEnv = initialState.knownTypes;
                   relationEnv = initialState.knownRels;
                   constructorEnv = initialState.knownConstrs;
                   boundNames = [];
                }.toAbella, initialCommands);
  --
  local outObligations::[ThmElement] =
        dropWhile((.is_nonextensible), obligations);
  local outThms::[(QName, Metaterm)] =
        foldl(\ rest::[(QName, Metaterm)] t::ThmElement ->
                rest ++ decorate t with {knownThms = rest;}.thms,
              initialState.knownTheorems, doThms);
  --
  return (commands, removeNonextensibleObligations(initialState));
}
