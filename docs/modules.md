# Extensibella Modules
Extensible languages used in Extensibella are built by modules.  Each
module can introduce new concrete and abstract syntax, new semantic
relations, new rules defining semantic relations, and new functions
for running the language.  Each module has its own proof file, which
can also introduce new properties and proof-level definitions.  All
modules are treated the same, whether they conceptually represent a
host language or extension, as the distinction is not clear in
Extensibella.


## Building on Modules
Conceptually, modules build on each other, adding to the constructs
and properties introduced in the modules on which they build.  The
building-on of language definitions is handled in the encoding of the
language definitions, not in Extensibella itself.

Extensibella handles building on the properties of other modules by
requiring each imported property be given the portions of its proof
required to be given by the new module.


## Qualified Names
Each language construct, property, and proof-level definition is
written using a short name, but also has a full, qualified name.  For
example, we might give a property named `typeUnique` in a module
`lang:host`.  While we can use the name `typeUnique` to refer to this
property, its full name is qualified by the name of the module giving
it, so we have `lang:host:typeUnique`.  We can use this full name
wherever we can use the short name.  In an extension `lang:ext` that
builds on `lang:host`, we can use either `typeUnique` or
`lang:host:typeUnique` when using this property.  This naming scheme
was inspired by
[Silver](https://melt.cs.umn.edu/silver/concepts/modules/#names).

The reason we qualify names is so a language with two extensions
introducing the same short name does not have a conflict when they are
used together.  Suppose both module `a` and module `b` introduce
`name`.  If we did not have qualified names, another module building
on both `a` and `b` would have two `name`s without a way to
differentiate them.  However, with qualification these become `a:name`
and `b:name`, so the third module can refer to each unambiguously.
