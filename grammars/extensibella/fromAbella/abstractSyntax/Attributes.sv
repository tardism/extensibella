grammar extensibella:fromAbella:abstractSyntax;


imports extensibella:common:abstractSyntax;


--Whether a proof state is during a proof or not
synthesized attribute inProof::Boolean;


--The proof state of a full display
synthesized attribute proof::ProofState;

--Gathering hypotheses in the current proof
synthesized attribute hypList::[(String, Metaterm)];

--Whether an error occurred
synthesized attribute isError::Boolean;
--Whether a warning occurred
synthesized attribute isWarning::Boolean;

--Whether an open proof was ended (completed or aborted)
synthesized attribute proofEnded::Boolean;

