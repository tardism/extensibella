grammar extensibella:common:abstractSyntax;


synthesized attribute pp::String;
flowtype pp {} on Subgoal,  Hypothesis, Context, CurrentGoal, ProofState, Metaterm, Term, TermList;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;
flowtype isAtomic {} on Metaterm, Term;


--The arguments in a TermList, but in an actual list
synthesized attribute argList::[Term];


--Whether a premise should be hidden
--We include this here because we need it in both toAbella and fromAbella
synthesized attribute shouldHide::Boolean;


--The goal we are currently trying to prove, if there is one
synthesized attribute goal::Maybe<Metaterm>;



--Names which occur anywhere in a term or metaterm, including uses and bindings
--(May include unbound names or names which are bound but used nowhere)
monoid attribute usedNames::[String] with [], ++;
propagate usedNames on
   Metaterm, Term, TermList, ListContents, PairContents,
      Hypothesis, Context, CurrentGoal, ProofState
   excluding bindingMetaterm, nameTerm;



--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;

