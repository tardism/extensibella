# Extensibility in Extensibella
Other documents discuss the general [notion of extensible
languages](extensible_languages.md) on which Extensibella is based and
[how we can prove properties of these languages
modularly](modular_reasoning.md).  Here we take the general theory and
explain how it is implemented in Extensibella.


## Extensible Languages in Extensibella
As discussed [elsewhere](extensible_languages.md), extensible languages
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
**NOTE:  Extensibella's proof scheme for extensible theorems is
currently guaranteed to be sound only for properties introduced by a
host language module (a module that doesn't import anything) or an
extension module that builds directly on the host language (a module
that only imports one module).  There is no error message for
introducing properties beyond this, and it is a deficiency we plan to
handle soon.**

Extensible theorems are used to prove properties about extensible
relations by considering the rules defining the relations.  An
extensible theorem is declared as
```
Extensible_Theorem <name> : forall <binds>,
   <hyp name> : <formula> ->
   <hyp name> : <formula> ->
   ...
   <conclusion> on <hyp name>.
```
Because these relations are extensible, not all the rules are known at
once, and the handling of the case analysis needs to be done
specially.  The `Extensible_Theorem` does this, guiding the user in
building an argument by induction and case analysis on the premise
chosen by the `on` clause, ensuring each proof case is handled.

The `on` clause must have the form `<rel> t1 ... tn`.  How the case
analysis is handled depends on the relationship between the module
where `<rel>`, the relation for the case analysis, was introduced; the
module where its primary component was introduced; and the module
where the property is introduced.

If the property, the relation, and its primary component type are all
introduced in the same module, then all modules introducing
constructors of the primary component and rules for the relation will
know the property exists and be able to prove the cases for the rules
they introduce.  In this case, the property introducing the extension
proves the cases for the rules it introduces when it declares the
extensible theorem.  Each extension module building on this one, when
it gives the `Prove` command for the theorem, is then presented with
the new cases it introduced for it to prove modularly.

If the property and the relation are both from one extension but the
primary component is from an imported module, some modules will
introduce new constructors of the primary component without knowing
the property exists.  However, the relation will be defined on them by
its copy rule, not by rules they write.  Then the declaration of the
extensible theorem presents the cases arising from the known rules for
the user to prove, as well as a preservability case where the relation
is defined for an explicitly unknown constructor (`<unknown ty>`)
using the copy rule.  Any modules that import this one will be
presented with the new cases introduced there to be proven upon
presenting the `Prove` command for this theorem.

The last case is one where the property is introduced by one module
but the relation is introduced by a module it imports.  In this case,
other extension modules may introduce new constructors for the
relation's primary component _and_ rules for the relation for them.
The declaration of the extensible theorem in this case relies on a
prior declaration of `Ext_Ind` for the relation, giving an error if
one is not found.  If it finds one, it will present the known cases
for the user to prove as before, as well as a case for explicitly
unknown constructs (`<unknown ty>`) based on the `Ext_Ind` declaration
for the relation, discussed in the next section.  Any modules that
import the one introducing this property will be presented with the
new cases introduced there to be proven upon issuing the `Prove`
command for this theorem.

### Extension Induction Proofs
A declaration of `Ext_Ind` has the form
```
Ext_Ind <rel> <rel args> with
   forall <binds>, <trans args> |{ty}- <original> ~~> <translation>.
```
Here the `forall` and bindings are optional, as there may be no new
variables to bind for the translation arguments.  This is declaring
that, whenever the relation `<rel>` holds, it will also hold on a
translation of the primary component with the same other arguments to
the relation.  For example, if we have a relation `eval` evaluating a
`tm` that takes no arguments to its translation and a declaration
```
Ext_Ind eval G T V with |{tm} T ~~> Trans.
```
we are requiring `eval G Trans V` to hold whenever `eval G T V` holds
and `T` translates to `Trans`, regardless of what `T` is, and that
this chain of translations does not go on forever.  This is a property
the user will be required to show.

The declaration of `Ext_Ind` must be given by the module writer
introducing the relation, and it comes with no work for that module
writer.  The issuing of the `Prove_Ext_Ind` command does come with
work.  First, for `Prove_Ext_Ind rel`, Extensibella creates relations
`<rel {ES}>` and `<rel {T}>`.  These are the extension size and
translation version of `rel`, respectively.  The extension size has
the same rules, other than adding a new integer argument that is
summed up for the sub-derivations in each rule, with the sum
incremented additionally if the rule is introduced by an extension.
The translation version of the relation has the same rules as the
original other than adding the translation assumption and relation
holding for the translation when the rule is introduced by an
extension.

To make this more concrete, consider a rule
```
rel A   rel B
-------------
 rel (c A B)
```
If this rule is introduced by the host language, we will introduced
these rules for the extension size and translation version:
```
<rel {ES}> A N1   <rel {ES}> B N2   N1 + N2 = N
-----------------------------------------------
             <rel {ES}> (c A B) N

<rel {T}> A   <rel {T}> B
-------------------------
    <rel {T}> (c A B)
```
If the original rule were introduced by an extension instead, we would
add these rules:
```
<rel {ES}> A N1   <rel {ES}> B N2  N1 + N2 + 1 = N
--------------------------------------------------
               <rel {ES}> (c A B) N

<rel {T}> A   <rel {T}> B   |{ty}- (c A B) ~~> R   <rel {T}> R
--------------------------------------------------------------
                      <rel {T}> (c A B)
```

The property the user proves using these definitions is
```
forall x n, <rel {ES}> x n -> <rel {T}> x
```
The user proves this using nested induction on `n` and the derivation
of `<rel {ES}>`.  The finer points of how to accomplish this reasoning
in Extensibella are best understood by walking through an example of
the reasoning, found in the examples linked [here](../README.md),
rather than by an explanation.

When an extensible theorem is declared that uses `Ext_Ind`, the case
for the explicitly unknown constructs assumes the translation as given
by the `Ext_Ind` declaration and that the relation holds on it.  For
example, for
```
Ext_Ind eval G T V with |{tm}- T ~~> Trans
```
will start with the assumptions
```
|{tm}- <unknown tm> ~~> Trans
```
and
```
eval G Trans V
```
to prove the property holds with an initial derivation of
`eval G <unknown tm> V`.
