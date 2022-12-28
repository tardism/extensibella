grammar extensibella:main;


function handleIncomingThms
--(commands for filling in anything imported,
-- updated prover state without the obligations we handled)
([AnyCommand], ProverState) ::= initialState::ProverState
{
  local obligations::[ThmElement] = initialState.remainingObligations;
  --
  local doThms::[ThmElement] =
        takeWhile((.is_nonextensible), obligations);
  --don't need toAbella here because it should already be valid
  local commands::[AnyCommand] =
        flatMap(\ t::ThmElement -> t.encode, doThms);
  --
  local outObligations::[ThmElement] =
        dropWhile((.is_nonextensible), obligations);
  local outThms::[(QName, Metaterm)] =
        foldl(\ rest::[(QName, Metaterm)] t::ThmElement ->
                rest ++ decorate t with {knownThms = rest;}.thms,
              initialState.knownTheorems, doThms);
  --
  return (commands,
          proverState(initialState.state, initialState.debug, outThms,
                      outObligations, [], [], []));
}
