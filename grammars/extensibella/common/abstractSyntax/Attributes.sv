grammar extensibella:common:abstractSyntax;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;

{-
  Attribute pp is from silver:langutil:pp.  We use this to get the
  easy wrapping it provides, which is necessary as formulas can get
  quite long.

  Attribute pp uses colons for joining QNames, where abella_pp uses
  the encoded separator name_sep for joining QNames.
-}

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

--Constructor building a term, if one exists
synthesized attribute headConstructor::QName;

--Whether a term is the unknown constructor standing in for
--constructors from other extensions
synthesized attribute isUnknownTerm::Boolean;

--Whether a term is built by constructors all the way down
synthesized attribute isConstant::Boolean;


--Split into a list along the given production
synthesized attribute splitConjunctions::[Metaterm];
synthesized attribute splitImplies::[Metaterm];


--Substitute a term for a name
inherited attribute substName::String;
inherited attribute substTerm::Term;
synthesized attribute subst<a>::a;


--Unify the top-level structure, getting a set of new equations
inherited attribute unifyWith<a>::a;
synthesized attribute unifySuccess::Boolean;
--only access these if unifySuccess is true
synthesized attribute unifyEqs::[(Term, Term)];
synthesized attribute unifySubst::[(String, Term)];



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

--typing substitutions
inherited attribute downSubst::Substitution;
synthesized attribute upSubst::Substitution;
--variable types
inherited attribute downVarTys::[(String, Type)];

--type variables generated as part of typing
monoid attribute tyVars::[String] with [], ++;
propagate tyVars on
   Type, TypeList, Term, TermList, Metaterm,
   PairContents, ListContents;

synthesized attribute isExtensible::Boolean;

