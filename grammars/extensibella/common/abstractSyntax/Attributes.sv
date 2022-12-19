grammar extensibella:common:abstractSyntax;


synthesized attribute pp::String;
flowtype pp {} on Subgoal,  Hypothesis, Context, CurrentGoal, ProofState, Metaterm, Term, TermList;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;
flowtype isAtomic {} on Metaterm, Term;


--Pass around information about the language with which we are working
--Decorated for efficiency
inherited attribute languageCtx::Decorated LanguageCtx;


--The arguments in a TermList, but in an actual list
synthesized attribute argList::[Term];


--The goal we are currently trying to prove, if there is one
synthesized attribute goal::Maybe<Metaterm>;



--Names which occur anywhere in a term or metaterm, including uses and bindings
--(May include unbound names or names which are bound but used nowhere)
monoid attribute usedNames::[String] with [], ++;
propagate usedNames on
   Metaterm, Term, TermList, ListContents, PairContents,
      Hypothesis, Context, CurrentGoal, ProofState
   excluding bindingMetaterm, nameTerm;

--Names bound by a binder
inherited attribute boundNames::[String];



--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;

