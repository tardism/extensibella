grammar extensibella:toAbella:abstractSyntax;

imports extensibella:common:abstractSyntax;

--translation to pass commands to Abella
synthesized attribute toAbella<a>::a;


--errors and warnings we encounter while translating
monoid attribute toAbellaMsgs::[Message] with [], ++;


synthesized attribute isUndo::Boolean;
synthesized attribute isQuit::Boolean;


--theorems currently being proven
synthesized attribute provingTheorems::[(QName, Metaterm)];
--commands that need to happen at points in the proof of an ext thm
synthesized attribute duringCommands::[(SubgoalNum, [ProofCommand])];
--commands that need to happen after a proof completes
synthesized attribute afterCommands::[AnyCommand];


--information about the current state of the prover
inherited attribute proverState::ProverState;

--the number of commands and resulting states in reverse order
--first element is current state
inherited attribute stateListIn::[(Integer, ProverState)];
--modified state list produced by command
synthesized attribute stateListOut::[(Integer, ProverState)];

--proof state produced after a command
inherited attribute newProofState::ProofState;
