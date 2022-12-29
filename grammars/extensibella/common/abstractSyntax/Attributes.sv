grammar extensibella:common:abstractSyntax;


--pp using colons for joining
synthesized attribute pp::String;
flowtype pp {} on Subgoal,  Hypothesis, Context, CurrentGoal,
                  ProofState, Metaterm, Term, TermList;
--pp using name_sep for joining
synthesized attribute abella_pp::String;
flowtype abella_pp {} on Metaterm, Term, TermList;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;
flowtype isAtomic {} on Metaterm, Term;


inherited attribute currentModule::QName;


inherited attribute typeEnv::Env<TypeEnvItem>;
inherited attribute constructorEnv::Env<ConstructorEnvItem>;
inherited attribute relationEnv::Env<RelationEnvItem>;


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


--Whether a term is built by some constructor rather than being a var
synthesized attribute isStructured::Boolean;
--Combination of isStructured for term lists
synthesized attribute isStructuredList::[Boolean];



--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;


--Turn a list-like thing into a list
synthesized attribute toList<a>::[a];
--Length of list-like things
synthesized attribute len::Integer;



synthesized attribute name::QName;

synthesized attribute type::Type;
synthesized attribute types::TypeList;

synthesized attribute isExtensible::Boolean;

