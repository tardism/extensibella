# Modular Reasoning
The purpose of Extensibella is to allow us to prove properties about
extensible languages in a modular fashion.  Each language module may
introduce its own properties, providing some portion of a proof for
them, as well as providing some portion of the proof for properties
from the modules it imports.  Extensibella ensures the proof work
provided by each module will work together so a full proof of each
property can be built using this modular proof work without needing
human intervention.

There are two pieces to ensuring the modular proof work will be valid
for proving the property for any composed language:
* The proof work must have the same effects in the context of the
  composed language as in the context of the module in which it was
  written.
* All cases in the composed language must be proven by some modular
  proof work.

We will discuss these both, assuming a single host language and
extensions that do not build on each other.  We furthermore assume all
relations introduced by extensions give the basic form of projection
rule, where the relation is copied directly from the projection of
its primary component.


## Ensuring Proof Work Remains Valid
We want the proof work written in the context of a single module and
the modules on which it builds to remain valid in the composed
language, meaning it proves the same sequents.  The difference between
the two contexts is that the latter's language may include more
language constructs, relations, and rules for existing relations, as
well as that we might have more properties we may use as lemmas in the
composition.  Then the only actions we might take in a proof that
could have different effects in the composed language are those that
rely on the language specification.

Since any rules we had before still apply, applications of rules are
not affected, and we need no restriction on them.

The only proof operation that might change is case analysis on a
derivation of a relation.  Since more rules may exist in a composed
language, a naive case analysis may create more cases in the context
of a composed language than in the context of a module and its
imports.  This would be a problem, as the extra cases would not have
proofs to handle them, and the composed language would not have a full
proof.

To ensure this does not happen, we restrict case analysis within
modular proofs.  Specifically, we restrict it to analyze only
derivations where the primary component of the relation derived is
built by a known constructor.  Recall from [our discussion of
extensible languages](extensible_languages.md) that new rules written
for an imported relation in a module must have the primary component
built by new syntax constructors also from that module.  This prevents
new rules from being added in further extension modules that will
apply to known syntax, and thus we know, in the context of a module
and its imports, all the cases that might apply in such a case even
when we move to the context of a composed language.


## All Cases Proven
Language properties are generally proven using induction and case
analysis in a central way, and we adopt this approach for our
properties as well.  Properties are proven arguing by induction and
case analysis on the derivation of a relation.  The cases arising from
this case analysis are distributed across the modules that know the
property, with how they are distributed depending on whether the
property is introduced by the host language or an extension, and, for
extension-introduced properties, whether the primary component of the
relation is introduced by that extension or the same host language.

### Host Language Property
If the property is introduced by the host language, all modules will
know the property exists.  In this case we can distribute the proof
work across all the modules in the language.

Each module is responsible for providing modular proof work that the
property holds in the cases arising from rules it introduces.  Since
each case in the language composition arises from a rule that is given
by one of the modules, and the module giving it must have provided
modular proof work showing the property holds in that case, each case
is proven in the composed language.  Then the composed language has a
full proof of the property.

### Extension Property with Extension Primary Component
If the primary component of the relation is introduced by the
extension introducing the property, the extension knows all the rules
defining the relation.  Then it can fully prove the property by itself
without considering extensibility, other than the restrictions on case
analysis mentioned above.

### Extension Property with Host Primary Component
If the relation's primary component is introduced by the host language
and the property is introduced by an extension, there can be other
extensions introducing new constructors of the primary component that
do not know the property to prove any portion of it.  Instead, the
extension introducing the property must prove it will hold in those
unknown cases as well.

Even here, a subset of the possible cases will be known.  The
extension introducing the property will know some of the rules for it,
both defined in that extension and any imported.  It provides modular
proof work showing the property will hold in the proof cases arising
from those rules.

The unknown cases are grouped together as a single proof case the
extension introducing the property must show.  This proof case is
called *preservability*.  The idea is to show the property copies back
from the primary component's projection, assuming a derivation of the
relation on the projection with which we can use the inductive
hypothesis.

If the relation is introduced by the current extension, we can see
that the assumptions of the preservability proof match the premises of
the projection rule that will be used to define the relation in the
unknown cases.  However, this is not the case if the relation is
introduced by the host language, as the rules for it in unknown cases
are given by the extensions introducing those cases.  In this case,
the host language must have introduced a property that the relation
will hold on the projection of the primary component in cases
introduced by an extension, and that this chain of projections
existing for the derivation ends.  Each extension proves this is true
for its constructs.  Then, in the language composition, the unknown
cases will satisfy the assumptions of preservability, and all the
cases will have proofs.
