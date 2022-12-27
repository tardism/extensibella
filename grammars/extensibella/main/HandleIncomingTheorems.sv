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
  local translated::[AnyCommand] =
        flatMap(\ t::ThmElement ->
                  flatMap(\ a::AnyCommand -> a.toAbella, t.encode),
                doThms);
  --
  local outObligations::[ThmElement] =
        dropWhile((.is_nonextensible), obligations);
  local outThms::[(QName, Metaterm)] =
        foldl(\ rest::[(QName, Metaterm)] t::ThmElement ->
                rest ++ decorate t with {knownThms = rest;}.thms,
              initialState.knownTheorems, doThms);
  --
  return (translated,
          proverState(initialState.state, initialState.debug, outThms,
                      outObligations, [], [], []));
}
