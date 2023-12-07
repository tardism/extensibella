grammar extensibella:toAbella:abstractSyntax;

imports extensibella:common:abstractSyntax;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;

--translation to pass commands to Abella
synthesized attribute toAbella<a>::a;


--errors and warnings we encounter while translating
monoid attribute toAbellaMsgs::[Message] with [], ++;


synthesized attribute isUndo::Boolean;
synthesized attribute isQuit::Boolean;


--whether this is running interactively or in a finished state
inherited attribute interactive::Boolean;


--theorems proven by a command as part of what it does
--different from provingTheorems because they are done, not being proven
synthesized attribute newTheorems::[(QName, Metaterm)];


--theorems currently being proven
synthesized attribute provingTheorems::[(QName, Metaterm)];
--extInds currently being proven
synthesized attribute provingExtInds::[(QName, [String], [Term],
                                        QName, String, String)];
--commands that need to happen at points in the proof of an ext thm
synthesized attribute duringCommands::[(SubgoalNum, [ProofCommand])];
--commands that need to happen after a proof completes
synthesized attribute afterCommands::[AnyCommand];


--[(relation, module defining primary component constructor)]
synthesized attribute relationClauseModules::[(QName, QName)];


--information about the current state of the prover
inherited attribute proverState::ProverState;

--the number of commands and resulting states in reverse order
--first element is current state
inherited attribute stateListIn::[(Integer, ProverState)];
--modified state list produced by command
synthesized attribute stateListOut::[(Integer, ProverState)];

--whether the tree being processed should ignore errors in determining
--whether definitions succeed
inherited attribute ignoreDefErrors::Boolean;

--proof state produced after a command
inherited attribute newProofState::ProofState;
