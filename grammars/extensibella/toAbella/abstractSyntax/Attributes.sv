grammar extensibella:toAbella:abstractSyntax;

imports extensibella:common:abstractSyntax;

--translation to pass commands to Abella
synthesized attribute toAbella<a>::a;

--information about the current state of the prover
inherited attribute proverState::ProverState;
