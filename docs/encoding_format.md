
In order for Extensibella to read encoded language specifications, the
specifications must follow an expected format.  This format gives
Extensibella the information it needs properly to handle
extensibility.

All definitions are put into a single definition file.  This
definition file contains the definitions for the module "officially"
being encoded, but also the definitions from the modules it imports,
all combined.




Qualified Names
======================================================================
Names are qualified by the module in which they occur, as discussed in
[modules.md]().  These are displayed to the user using colons as
separators, with modules also possibly being qualified.

In the encoding into Abella, such qualified names have the colons
replaced by `-$-`, so we get `mod-$-du-$-le-$-name`.
This is used in the encoded Abella definitions whenever we
want to refer to the item with this name.

Because we can use the short name alone in Extensibella, in order to
distinguish
between meta-variables and short names, all short names should be
lowercase.




Language Syntax
======================================================================
We assume the language syntax is defined by a grammar, specifically
named nonterminals and named productions.

Nonterminals
----------------------------------------------------------------------
We name nonterminals of the language using their qualified names with
a prefix, so `mo:du:le:Nt` is named as `$ty__mo-$-du-$-le-$-Nt`.

Nonterminals are defined as Abella types of kind `type`, so we define
nonterminals as
```
Kind $ty__mo-$-du-$-le-$-Nt   type.
```
We might add the ability to have functor nonterminals (e.g. have kind
`type -> type`), but this is not currently present.


Productions
----------------------------------------------------------------------
We name productions using their qualified names, so `mo:du:le:prod` is
named as `mo-$-du-$-le-$-prod`.

Productions are defined in Abella as constructors.  If a production
`mod:prod` takes arguments of nonterminal types `mod1:A` and `mod2:B`
and builds a `mod:C`, we encode it as
```
Type mod-$-prod   $ty__mod1-$-A -> $ty__mod2-$-B -> $ty__mod-$-C.
```

Module definition files must also include appropriate generic
constructors.  If a module `mod` imports a module `imp` introducing a
nonterminal `imp:Nt`, the definition must include a new production as
```
Type $unknownI__imp-$-Nt   $ty__imp-$-Nt.
```
This is a placeholder for productions of the `imp:Nt` nonterminal
introduced by other modules not known to the current module and will
be used in defining and reasoning about extensible relations.

If a module `mod` imports a module `imp` introducing an extensible
relation `imp:rel` with primary component `imp:Nt`, the definition
must include a new production as
```
Type $unknownK__imp-$-rel   $ty__imp-$-Nt.
```
This is also a placeholder for productions of the `imp:Nt` nonterminal
introduced by other modules, but specifically for those where the
`imp:rel` relation is defined for them by the module introducing them.




Extensible Relations
======================================================================
Extensible relations are relations defined around a primary component
(of a nonterminal type `Nt`) that may have new rules added by further
modules that add new productions building the type `Nt`.  These are in
contrast to fixed relations that cannot have new rules added.

An extensible relation `mod:rel` is defined as a relation in Abella.
If `mod:rel` takes arguments of types `a`, `b`, and `c` where `b` is
the primary component, we give a definition as
```
Define $ext__1__mod-$-rel : a -> b -> c -> prop by
...
```
where we fill in the clauses as appropriate.  Notice that the relation
name includes the zero-based index of the primary component.  This is
necessary for communicating to Extensibella which argument is the
primary component.

Any relations that are mutually-recursive need to be defined in the
same definition block.  That is, if we have relations `a`, `b`, and
`c` that each define themselves in terms of the other, they must be
defined as
```
Define $ext__pca__a : <args a> -> prop,
       $ext__pcb__b : <args b> -> prop,
       $ext__pcc__c : <args c> -> prop by
...
```
The clauses for all the relations are then filled in as appropriate.

We consider two types of extensible relations,
host-language-introduced relations and extension-introduced relations.
This might seem strange, since we don't actually have a separation
between "host" and "extension" modules.  The host-ness or
extension-ness of an extensible relation is determined by the module
in which it is defined and the module in which the primary component
is defined.  If they are the same, it is treated as a host relation;
otherwise, it is defined as an extension relation.  For example, if we
define a relation `host:rel` with the primary component `host:Nt`,
then it is a host relation.  If we define a relation `ext:rel` with
the primary component `host:Nt`, this is an extension relation.


Host Relations
---------------------------------------------------------------------
Host relations in general require nothing extra beyond what we have
already discussed.  However, we consider two special host relations,
the Abella `is` relation and the projection relation.

Abella reasoning traditionally relies heavily on `is` relations
defining the members of a type.  These are not strictly required in
definition files for Extensibella, but are probably a good idea.
Because types can be extended, these should be introduced as host
relations.

A module `mod` must define a projection relation for each nonterminal
`Nt` it introduces.  Even if none of the productions the module
introduces project, it must define this relation so extensions to
the module may write rules for it for the constructs they introduce.
If the projection relation for `mod:Nt` takes one argument, of type
`a`, to define the projection, its projection relation must be
defined as
```
Define $proj__mod-$-Nt : a -> $ty__mod-$-Nt -> $ty__mod-$-Nt -> prop by
...
```
The first `mod:Nt` argument is the projecting syntax and the second
`mod:Nt` is the projected-to syntax.


Extension Relations
----------------------------------------------------------------------
Extension relations are defined as above, but must also include a
special clause.  Recall extension-introduced relations are defined by
a default rule for constructors of the primary component from other
extensions.  Each extension-introduced relation must have a clause for
the generic constructor (e.g. `$unknownI__imp-$-Nt`).  These clauses
are expected to be at the end of the definition, after all other
clauses for the relation.


Importing Relations
----------------------------------------------------------------------
Recall that we combine the new and imported definitions into a single
definition file.  In doing so, the order of imported clauses for a
relation must be maintained.  This is so the proofs written in one
component will remain valid by order in the composition.

For the same reason, if modules `C` and `D` both import modules `A`
and `B`, the clauses from `A` and `B` must be in the same order
relative to one another in the definition files for both `C` and `D`.
It cannot be that `A`'s clauses come first in one file and `B`'s
clauses come first in the other.

We must also fill in projection clauses for extension relations with
concrete terms as we import relations into new modules.  Suppose we
have a module `ext1` defining a relation `ext1:rel` with primary
component `host:Nt`.  Suppose we have a module `ext2` that also
imports `host` and has a production `ext2:prod` with two arguments.
Finally, suppose `comp` imports both `ext1` and `ext2`.  In the
definition file for the `comp` module, we must take the projection
rule for `ext1:rel` and add clauses filling in the projection rules
with `ext2:prod A B` for the primary component.  This allows any
reasoning in the `comp` module about `ext1:rel` to take advantage of
the knowledge that the rule for this relation when the primary
component is built by `ext2:prod` uses these projection rules, and is
necessary for a correct definition and reasoning.

Finally, we must fill in a stand-in rule for any imported relation
standing in for the rules introduced by unknown extensions to be used
to show the property will hold for them when using a declaration of
`Ext_Ind` to allow induction on an imported relation for a new
property.  For a relation `mod:rel` with three arguments where the
second one is the primary component, this would be a definition clause
as follows:
```
$ext__1__mod-$-rel A $unknownK__mod-$-Nt B :=
   exists <vars>, <def> /\ (($posInt $zero = $posInt $zero) -> false).
```
Here `<def>` stands for the premises of the stand-in rule, and
`<vars>` includes any bindings needed for those premises.  The reason
we include the `($posInt $zero = $posInt $zero) -> false` premise
(`0 = 0 -> false`) is to prevent Abella from using this rule to show
the relation holds for the generic constructor.  Without this, Abella
might use this rule to show the relation holds for the generic
constructor; since the rules given by the other extensions for which
this rule is standing in will not have this form, that would be
invalid.  Adding this impossible assumption prevents Abella from doing
so.




Fixed Relations
======================================================================
Fixed relations are relations that may not have their rules extended
by modules importing the module in which the relation is defined.
Because they are not extended, they do not have a primary component.

A fixed relation `mod:rel` is defined as a relation in Abella, as
extensible relations are.  If `mod:rel` takes arguments of types `a`,
`b`, and `c`, we give a definition as
```
Define $fix__mod-$-rel : a -> b -> c -> prop by
...
```
where we fill in the clauses as appropriate.




Encodings for Full Languages
======================================================================
If we want to build a composed proof for the language of a module,
Extensibella requires a full language encoding.  This is nearly the
same as the encoding discussed thus far.  However, it does not include
the generic constructors or rules for them.

It adds one feature, a definition with the sole purpose of passing
along information about the stand-in rule (i.e. the one used for the
generic `$unknownK__mod:rel` constructor).  This has the form
```
Define $stand-in_rule__mod-$-rel : a -> b -> c -> prop by
$stand-in_rule__mod-$-rel A B C := <def>.
```
for a relation `mod:rel` with argument types `a`, `b`, and `c` and a
stand-in rule defined by premises given by `<def>`.
