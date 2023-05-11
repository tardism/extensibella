# Extensibility in Extensibella
Other documents discuss the general [notion of extensible
languages](extensibleLanguages.md) on which Extensibella is based and
[how we can prove properties of these languages
modularly](modularReasoning.md).  Here we take the general theory and
explain how it is implemented in Extensibella.


## Extensible Languages in Extensibella
As discussed [elsewhere](extensibleLanguages.md), extensible languages
are built by modules introducing syntax and semantics, where both may
be extended by other modules building on those modules.

The module specification used in an Extensibella session includes
language types, constructors of those types, and relations.  All of
these are extensible.

### Constructors
The constructors of a type in a language are extensible, and we
recognize this fact by including a constructor `<unknown ty>` for each
type known in the language module.  This constructor is a placeholder
for the constructors that can be introduced by other modules, standing
generically for all of them.

### Relations
The relations in a module are split into two categories, extensible
and fixed.

Extensible relations are ones to which new rules may be added by
modules building on the module introducing the relation.  This is
generally how language semantics are written so new definitions of
them may be given for new syntax.

Fixed relations are given all their rules in the module introducing
the relation; other modules cannot add rules defining them.  This
sounds like it is not in the spirit of an extensible language, and
overuse of them does lead to languages that have limited
extensibility.  However, they are useful in certain cases.  For
example, if we want to use another relation across a list of items, we
can use a fixed relation to walk across the list.  If we want to check
the types of a list of expressions using an extensible `typeOf`
relation, we can use a fixed relation to walk across the list without
losing the actual extensibility in the expressions and their typing.


## Modular Reasoning in Extensibella
Reasoning in Extensibella is made up of extensible and non-extensible
elements.  Extensible elements prove things about extensible
relations, with proof work that is potentially distributed across
multiple modules.  These are declared using the `Extensible_Theorem`,
`Translation_Constraint`, and `Ext_Ind` top-level commands.

Non-extensible elements do not have work that might need to be
extended; any work associated with it is constant and can be done in a
single module.  These are declared using the other top-level commands
in the language, such as `Theorem`, `Split`, and `Define`.  There are
several reasons we might use non-extensible elements.  For example:
* We might need a relation for a proof that is not used in the
  language, such as a relationship between a typing and evaluation
  context.  We can define this as a proof-level relation using
  `Define`.
* We might have a fixed relation in the language about which we want
  to prove a property, which we can do using a `Theorem` declaration.
* We might have a property proven using `Extensible_Theorem` but we
  want to specialize it or show a corollary to it, and we can declare
  the new version of it using `Theorem`.

### Element Ordering
As we might expect, the extensible and non-extensible elements in an
Extensibella development occur in a particular order, with the
theorems and definitions given earlier in the ordering being available
later in the ordering.

When we want to build an Extensibella development for a module that
imports others, we need to incorporate the orders of elements from
those modules into the current one.  Extensibella reads all the orders
of the imported modules and computes a safe ordering in which to
include all the imported elements, one in which each imported order is
maintained while potentially adding new elements from other imported
orders.  If Extensibella encounters `Prove` elements in a different
order than the expected one, it gives an error.  To aid in getting the
right order, Extensibella can be used to generate a skeleton of the
required `Prove` commands in the correct order (discussed
[here](running.md)).

Only the extensible imported elements are mentioned explicitly in the
module importing them.  The others are left implicit and are added as
soon as their preceding extensible elements have their new modular
proof work completed.  For example, suppose an imported module had as
part of its element order
```
Extensible_Theorem e : ...
Define r : ...
Theorem t : ...
```
In the importing module, as soon it finishes its modular proof work
for `e`, the definition of `r` and the theorem `t` are entered, and
can be used immediately in the next element in the development.

A module may freely add new elements, both extensible and
non-extensible, between the extensible obligations from imported
elements.  These may use any earlier imported elements, and may be
used to write modular proof work for any later imported elements.

### Translation Constraints
Translation constraints declare how we expect the semantics of a new
construct to relate to its translation's semantics.  Their purpose is
to inform the authors of extension modules what they may expect from
the constructs introduced by other extensions.  For example, an
extension introducing a new static analysis, which will be defined on
the constructs from other translations via copying from the
translation, will want to know how evaluation is related between an
unknown construct and its translation, to know whether the definition
by copying will be a sensible one.

Translation constraints are defined thus:
```
Translation_Constraint <name> : forall <binds>,
   <hyp name> : <trans args> |{<ty>}- <original> ~~> <translation> ->
   <hyp name> : <formula> ->
   ...
   <conclusion>.
```
Translation constraints are proven by considering the rules defining
the translation.  Because translations are schematic and are not
inductive, no induction is used to build the argument.  If a user
finds he needs induction to argue for a particular translation case,
he can generally accomplish this by declaring a non-extensible theorem
for his particular case and proving that using induction.

### Extensible Theorems



TODO

Things to talk about:
* Extensible theorems
  + Currently only guaranteed sound for properties for a single host +
    extensions that don't build on each other
  + Extensibella does not complain if you break this
* Ext_Ind
