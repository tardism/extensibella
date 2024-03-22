# Extensible Languages
The view of extensible languages on which Extensibella is based is one
in which the language's syntax and semantics are given by a base
language, or host language, and a set of independently-developed
extensions adding to its definitions.


## Basic Extensible Languages
In a basic formulation of language extensibility, the base language
can introduce the following:
* Syntactic categories
* Constructors building those syntactic categories
* Semantic relations
* Rules defining those semantic relations

Extensions can then build on these by introducing the following:
* New constructors of the base language's syntactic categories
* New rules defining the base language's relations
* New syntactic categories
* Constructors building those new syntactic categories
* New semantic relations
* Rules defining those new semantic relations

A composed language is built by combining the base language with a set
of extensions.  The composed language contains all the syntax and
semantics given by the base language and each extension.

### Composing New Syntax and New Semantics
Notice that we have independent extension on two fronts, in both the
syntax and the semantics of our language.  How, when one extension
adds a new semantic relation, do we define it on the new syntax
constructors introduced by another extension?  This is part of Phil
Wadler's famous *expression problem*.  One option is to say the
relation is not derivable on the new constructors.  However, this
would make the combination of new syntax and new semantic relations
unusable in practice, since a new static safety check, for example,
would never hold if a program included new syntax from a different
extension.

The solution we use allows a new relation from one extension to
be defined on new syntax from another extension.  This solution relies
on the notion of the primary component of a relation, given when the
relation is declared.  The primary component is the argument to the
relation that the relation is *about*.  For example, a typing relation
is *about* the expression being typed, with the typing context and
type produced being secondary.

Each relation introduced by an extension where the primary component
is a syntactic category given by the base language is given a special
rule, called its projection rule, to define it on new syntax from
other extensions.  This rule is written with a variable in the place
of the primary component.  For example, we might have an `optimize`
relation reducing constant computations in an expression, with the
projection rule stating optimizing an unknown expression leaves it as
it is:  `optimize E E` (a safe, if uninspiring, choice).  When a
composed language is built, combining several extensions, the
projection rule is replicated for each new constructor from other
extensions, filling in the primary component with the new
constructor.  For example, if other extensions introduced constructors
`add3(expr, expr, expr)` and `negate(expr)`, we would instantiate the
projection rule for each of these:
```
optimize add3(E1, E2, E3) add3(E1, E2, E3)
optimize negate(E) negate(E)
```
This gives the `optimize` relation a definition on any syntax, even
that not known to it when it was introduced.

Oftentimes a simple projection rule, as we saw with `optimize` above,
is not sufficient for defining an extension-introduced relation.
Generally what we want is to use a notion of projection of an unknown
construct to a known one (hence the name of the rules).  Each
syntactic category given by the base language has a projection
relation, and each constructor an extension introduces must have a
rule giving its projection to the base language.  Then the
projection rule for a relation can be written to find the projection
of the primary component and derive the relation on the projection.
This essentially copies the definition from the projection, and
allows more interesting relations to be defined in extensions.

### Limitations on Extending Relations from the Base Language
Defining new semantic relations in an extension relies on
understanding the semantics of the constructs from the base language.
For example, writing the `optimize` relation to reduce constant
computations such as `3 + 4` only works if we know that `3 + 4` must
always reduce to `7`.  If an extension could write a new rule for
evaluation allowing `3 + 4` to evaluate instead to another number, or
a different kind of value entirely, the optimization would no longer
accurately capture the language's semantics.

To ensure the semantics of the known language remain the same under
extension, new rules given in an extension defining a relation given
by the base language must have as the primary component of the
conclusion a new constructor.  For example, an extension adding an
`add3` constructor could define evaluation for it, but it could not
write a rule defining evaluation for the base language's addition.


## Expanding the Idea of Extensible Languages
Extensible languages as we have defined them thus far are built by a
base language and a set of extensions building directly on that
language, developed completely independently of each other.  However,
Extensibella expands this notion.  Rather than a base language and
extensions, we simply have a set of modules that may freely build on
each other.  These modules are developed independently, with knowledge
of only the modules they build on.  Thus, rather than a
spoke-and-wheels sort of module dependency graph, we can have a
directed acyclic dependency graph instead.

Rather than full modules being of the base or extension classes, each
constructor, rule, and relation is treated as either "base-y" or
"extension-y":
* A constructor is treated as part of the base language for its
  syntactic category if it is introduced in the same module as its
  category, or as part of an extension for its syntactic category if
  its category was introduced in a different module.  If it is part of
  an extension for its category, it must provide a projection.
* A rule is treated as part of the base language for its relation if
  it is given in the same module introducing the relation.  If it is
  part of an extension, its primary component must be built by a
  constructor also introduced in the current module.
* A relation is treated as "base-y" if it is introduced in the same
  module introducing its primary component syntactic category.  If
  not, then it is considered part of an extension and must provide a
  projection rule.

The contraction of the base and extension classes to apply to
individual elements of modules rather than applying to modules
themselves still ensures a well-formed composed language taken by
combining the modules.  It also gives more freedom in building
languages, as a further extension can be built on an existing
extension.
