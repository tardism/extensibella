grammar extensibella:toAbella:abstractSyntax;

imports extensibella:common:abstractSyntax;

--translation to pass commands to Abella
synthesized attribute toAbella<a>::a;


--errors and warnings we encounter while translating
monoid attribute toAbellaMsgs::[Message] with [], ++;


--information about the current state of the prover
inherited attribute proverState::ProverState;
