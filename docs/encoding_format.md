
In order for Extensibella to read encoded language specifications, the
specifications must follow an expected format.  This format gives
Extensibella the information it needs to properly handle
extensibility.

All definitions are put into a single definition file.  This
definition file contains the definitions for the module "officially"
being encoded, but also the definitions from the modules it imports,
all combined.




Qualified Names
======================================================================
Names are qualified by the module in which they occur.  These are
displayed using colons as separators, with modules also possibly being
qualified.  For example, we might have a module `mo:du:le` that
declares a name `name`.  This produces a fully-qualified name
`mo:du:le:name`.

In the encoding into Abella, such qualified names have the colons
replaced by `-$-`, so we get `mod-$-du-$-le-$-name` for our example
above.  This is used in the encoded Abella definitions whenever we
want to refer to the item with this name.




Language Syntax
======================================================================
We assume the language syntax is defined by a grammar, specifically
named nonterminals and named productions.

Nonterminals
----------------------------------------------------------------------
We name nonterminals using their qualified names, so `mo:du:le:Nt` is
named as `mo-$-du-$-le-$-Nt`.

Nonterminals are defined as Abella types of kind `type`, so we define
nonterminals as
```
Kind mo-$-du-$-le-$-Nt   type.
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
Type mod-$-prod   mod1-$-A -> mod2-$-B -> mod-$-C.
```

Suppose we are defining a module `mod` that imports a module `imp`.
Further suppose `imp` introduces a nonterminal `imp:Nt`.  Then the
definition must include a new production as
```
Type $unknown_imp-$-Nt   imp-$-Nt.
```
This is a placeholder for productions of the `imp:Nt` nonterminal
introduced by other modules not known to the current module and will
be used in defining extensible relations.




Extensible Relations
======================================================================
Extensible relations are relations defined around a primary component
(of a nonterminal type `Nt`) that may have new rules added by further
modules that add new productions building the type `Nt`.  These are in
contrast to fixed relations that cannot have new rules added.

An extensible relation `mod:rel` is defined as a relation in Abella.
If `mod:rel` takes arguments of types `a`, `b`, and `c`, we give a
definition as
```
Define $ext__mod-$-rel : a -> b -> c -> prop by
...
```
where we fill in the clauses as appropriate.

Because these relations are extensible, and therefore new rules might
introduce new dependencies between relations that were formerly
independent, all extensible relations must be defined in the same
definition block.  That is, if we have extensible relations `a`, `b`,
and `c`, they must be defined as
```
Define $ext__a : <args a> -> prop,
       $ext__b : <args b> -> prop,
       $ext__c : <args c> -> prop by
...
```
The clauses for all the extensible relations are then filled in as
appropriate.

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
the Abella `is` relation and the translation relation.

Abella reasoning traditionally relies heavily on `is` relations
defining the members of a type.  These are not strictly required in
definition files for Extensibella, but are probably a good idea.
Because types can be extended, these should be introduced as host
relations.

A module `mod` must define a translation relation for each nonterminal
`Nt` it introduces.  Even if none of the productions the module
introduces translate, it must define this relation so extensions to
the module may write rules for it for the constructs they introduce.
If the translation relation for `mod:Nt` takes one argument, of type
`a`, to define the translation, its translation relation must be
defined as
```
Define $trans__mod-$-Nt : a -> mod-$-Nt -> mod-$-Nt -> prop by
...
```
The first `mod:Nt` argument is the translating syntax and the second
`mod:Nt` is the translated-to syntax.


Extension Relations
----------------------------------------------------------------------
Extension relations are defined as above, but must also include a
special clause.  Recall extension-introduced relations are defined by
translation of the primary component.  Each extension-introduced
relation must have a clause (or several clauses, if there are multiple
translation rules) with these rules for the required unknown
constructor of the primary component (e.g. `$unknown_imp-$-Nt`).
These clauses must come after all other clauses for the relation.


Importing Relations
----------------------------------------------------------------------
Recall that we combine the new and imported definitions into a single
definition file.  In doing so, the order of imported clauses for a
relation must be maintained.  This is so the proofs written in one
component will remain valid by order in the composition.

We must also fill in translation clauses for extension relations with
concrete terms as we import relations into new modules.  Suppose we
have a module `ext1` defining a relation `ext1:rel` with primary
component `host:Nt`.  Suppose we have a module `ext2` that also
imports `host` and has a production `ext2:prod` with two arguments.
Finally, suppose `comp` imports both `ext1` and `ext2`.  In the
definition file for the `comp` module, we must take the translation
rule for `ext1:rel` and add clauses filling in the translation rules
with `ext2:prod A B` for the primary component.  This allows any
reasoning in the `comp` module about `ext1:rel` to take advantage of
the knowledge that the rule for this relation when the primary
component is built by `ext2:prod` uses these translation rules, and is
necessary for a correct definition and reasoning.




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

Unlike extensible relations, fixed relations need not all be defined
in the same block.  They can be defined as such, if desired.  They can
be defined as part of the block of extensible relations, if desired.
This can be helpful as it allows a defined relation that is shorthand
for some combination of extensible relations and to be used also to
define an extensible relation.
