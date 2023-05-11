# Extensibella Language
Extensibella is an interactive proof assistant based on
[Abella](http://abella-prover.org).  Much of the language will look
familiar to those familiar with Abella.


## Module Declaration
Each Extensibella interaction starts with a module declaration:
```
Module mo:du:le.
```
This loads the specification of the module named `mo:du:le`.  This is
the language module about which the session will reason.

Each session only works with one module declaration.  A new module
cannot be loaded later in a session; rather, one must exit
Extensibella and start a new interaction to start working with a new
module declaration.


## Basic Syntax
Extensibella's syntax is built on logical formulas, which in turn are
built on terms.  We look at each in turn.

### Formulas
Logical formulas are built by logical connectives over terms.  Their
syntax:
  | Formula Syntax               | Meaning                           |
  |------------------------------|-----------------------------------|
  | `forall A B C, ...`          | universal quantification          |
  | `exists A B C, ...`          | existential quantification        |
  | `F1 /\ F2`                   | conjunction                       |
  | `F1 \/ F2`                   | disjunction                       |
  | `F1 -> F2`                   | implication                       |
  | `true`                       | logical true                      |
  | `false`                      | logical false                     |
  | `rel t1 t2 t3`               | relation                          |
  | `t1 = t2`                    | equality of terms                 |
  | `t1 + t2 = t3`               | addition                          |
  | `t1 - t2 = t3`               | subtraction                       |
  | `- t1 = t2`                  | negation                          |
  | `t1 * t2 = t3`               | multiplication                    |
  | `t1 / t2 = t3`               | division                          |
  | `t1 mod t2 = t3`             | modular division                  |
  | `t1 ++ t2 = t3`              | append for lists or strings       |
  | `t1 < t2 = t3`               | less than                         |
  | `t1 <= t2 = t3`              | less than or equal to             |
  | `t1 > t2 = t3`               | greater than                      |
  | `t1 >= t2 = t3`              | greater than or equal to          |
  | `t1 \|\| t2 = t3`            | Boolean or                        |
  | `t1 && t2 = t3`              | Boolean and                       |
  | `!t1 = t2`                   | Boolean negation                  |
  | `t1, t2, t3 |{ty}- t ~~> t'` | translation of a term             |
  | `<rel {ES}> t1 t2 t3`        | extension size of a derivation    |
  | `<rel {T}> t1 t2 t3`         | translation version of a relation |

Using three terms for relations, including the extension size and
translation version, and for the arguments to translation, is just a
placeholder.  These can take an arbitrary number of arguments.  The
same is true for bindings, which make take an arbitrary number of
bound variables.  Variables may also be annotated with their types in
the bindings as `(v1 v2 : ty)`.

Any formulas that include an equals sign may also be flipped about the
equals sign (e.g. `t3 = t1 + t2` is equivalent to `t1 + t2 = t3`).

### Terms
The syntax of terms includes the same constructs as Abella, which are
constants, applications of constants, and abstractions, but it also
adds syntax for other useful constructs:
   | Term Syntax        | Meaning                 |
   |--------------------|-------------------------|
   | `<var>`            | variable                |
   | `c t2 ... tn`      | constructor application |
   | `t1::t2`           | cons list               |
   | `nil`              | empty list              |
   | `[]`               | empty list              |
   | `[t1, t2, ... tn]` | list literal            |
   | `(t1, t2, ... tn)` | tuple literal           |
   | `"<contents>"`     | string literal          |
   | `<integer>`        | integer literal         |
   | `true`             | Boolean true            |
   | `false`            | Boolean false           |

### Names and Comments
Identifiers (variables, theorem names, etc.) may begin with a letter
or one of ``-^=`'?`` followed by any letters, digits, symbols from the
previous list, or `_*@+#!~/`.  If an identifier starts with `=`, it
must be followed by another character.  Note that this also means
spaces in operations can be important (e.g. `t1 + t2 = t3` is an
addition formula, while `t1+t2=t3` is a single identifier).

Anywhere the short name of a construct can be used, the qualified name
can also be used (see [the discussion of modules](modules.md) for what
we mean by qualified names).  Then, for example, `mo:du:le:rel x y z`
and `rel x y z` may be used interchangeably, as long as there is not
another relation named `rel` available in the current module.

Single-line comments start with `%` and may begin anywhere in a line.
Multi-line comments are demarcated by `/*` and `*/`.


## Built-In Types
There are several built-in types and type constructors in
Extensibella, each with an appropriate `is` relation:
* List types, written `list T` where `T` is a type
  + `nil`, `[]`, `t1::t2`, `[t1, ... tn]` all have a list type
  + `is_list IsT` is the `is` relation for `list T`, where `IsT` is
    the `is` relation for `T`
* Pair types, written `pair T1 T2` where `T1` and `T2` are types
  + `(t1, ... tn)` has type `pair T1 (pair T2 ... (pair Tn-1 Tn)...)`
    where `ti` has type `Ti`
  + `is_pair IsT1 IsT2` is the `is` relation for `pair T1 T2`, where
    `IsT1` and `IsT2` are the `is` relations for `T1` and `T2`
* Integer type, written `integer`
  + `is_integer` is the `is` relation for integers
* String type, written `string`
  + `is_string` is the `is` relation for strings
* Boolean type, written `bool`
  + `is_bool` is the `is` relation for Booleans


## Top-Level Commands
Top-level commands are the commands that can be used outside of a
proof.

We borrow our basic ones from [Abella][1]:
* Theorem declaration:  `Theorem <name> : body.`
  + Declares a (non-extensible) theorem, causing Extensibella to enter
    its proof mode
  + Optionally, this may have type parameters, such as
    ```
    Theorem append_unique[Ty] : forall (L1 L2 L L' : list Ty),
       L1 ++ L2 = L -> L1 ++ L2 = L' -> L = L'.
    ```
    Once proven, this theorem could be used to show appending lists
    containing any type creates unique results.
* Definition declaration:  `Define <name> : <ty> by <clauses>.`
  + Defines a new fixed-point relation at the proof level
  + This creates a proof-level fixed definition (see the [document
    about extensibility](extensibility.md)), not an extensible one
  + May define multiple mutually-inductive relations together
* Split theorem:  `Split <name> as <names>.`
  + Splits a theorem with top-level conjunctions into separate
    theorems
  + For example, `Split thm as a, b, c.` where `thm` refers to the
    formula `f1 /\ f2 /\ f3` will create new theorems named `a`, `b`,
    and `c` where `a` refers to `f1`, `b` refers to `f2`, and `c`
    refers to `f3`
* Kind declaration:  `Kind <name> <kind>.`
  * Creates a new proof-level type
  * The kind is a kind as in [Abella][1]
* Type declaration:  `Type <name> <type>.`
  * Creates a new proof-level constructor with the given type
  * Must build a proof-level type, not a type in the language or a
    built-in type

We also have commands for working with extensible languages:
* Extensible theorem declaration:  `Extensible_Theorem <name> : forall
  <bindings>, <hyp name> : <formula> -> <hyp name> : <formula> ->
  ... <conclusion> on <hyp name>.`
  + Declares an extensible theorem to be proven, using induction and
    case analysis on the premise labeled with the name given at the
    end
  + The premise given at the end must have the form `rel t1 ... tn`
    where `rel` is an extensible relation and its primary component is
    built by a variable
  + Adds each premise to the context as a hypothesis with its given
    name
  + Multiple mutually-inductive theorems can be declared together by
    repeating the theorem declaration part (the theorem name through
    the `on` clause)
  + The details of extensible theorems are discussed in the [document
    about extensibility in Extensibella](extensibility.md)
* Translation constraint declaration:  `Translation_Constraint
  <name> : forall <bindings>, <hyp name> : <args> |{<ty>}- <original>
  ~~> <translation> -> <hyp name> : <formula> -> ... <conclusion>.`
  + Declares a translation constraint to be proven using case analysis
    on the translation
  + The details of translation constraints are discussed in the
    [document about extensibility in Extensibella](extensibility.md)
* Extension induction declaration:  `Ext_Ind <rel> <rel args> with
  forall <bindings>, <trans args> |{ty}- <original> ~~>
  <translation>.`
  + Declares a requirement for modules to show extensions can build
    arguments for new properties using the extensible relation `<rel>`
    for induction
  + Multiple relations can be combined by repeating the declaration
    portion (the relation to the end)
  + The need for this and details about it are discussed in the
    [document about extensibility in Extensibella](extensibility.md)

Each of these extensible top-level commands also has a `Prove`
version, used for adding to its proof in modules that build on the
module introducing it.  They are `Prove_Theorem`, `Prove_Constraint`,
and `Prove_Ext_Ind`, respectively.  Each of these takes a list of
qualified names (*not* short names) for the theorems, or, in the last
case, relations, to the proofs of which it is adding, and presents the
user with the new cases to prove in the current module.


## Proof Tactics
Tactics are the commands used within a proof to advance the proof
state.

We borrow our proof commands from [Abella][1]:
* Induction tactic:  `induction on <num>.`
  + Sets up an induction hypothesis and appropriate restriction on the
    `<num>`^{th} premise
  + For example, with a goal `forall x, R x -> Q x -> S x`, the
    command `induction on 2` will create an inductive hypothesis
    `forall x, R x -> Q x* -> S x` and will change the goal to
    `forall x, R x -> Q x@ -> S x`
  + Mutual induction across a conjunction can be declared by including
    multiple numbers (e.g. `induction on 3 2 4 1.`)
* Intros tactic:  `intros <names>.`
  + Pulls the premises of the goal into the context as hypotheses,
    giving them the given names
  + If not enough names are given, fresh names will be generated
* Apply tactic:  `apply <thm> to <hyps> with <var> = <tm>, ....`
  + Applies a formula, referenced by name, to the given hypotheses,
    giving specific instantiations of the variables listed at the end,
    adding the conclusion to the context as a hypothesis
  + The applied formula may be a previously-proven theorem or a
    hypothesis in the current context
  + The hypotheses to which it is applied may also include
    underscores, in which case Extensibella searches for a formula to
    fill them.  Any not found are added as subgoals for the user to
    prove
  + Variable instantiations are usually not needed and may be left
    off; they are helpful in conjunction with underscores to fill in
    terms that are otherwise not known
* Backchain tactic:  `backchain <thm> with <var> = <tm>, ....`
  + Unifies the conclusion of the formula with the current goal and
    searches for solutions to the premises
  + The formula may be a previously-proven theorem or a hypothesis in
    the current context
  + If the premises are not found, they are added as subgoals for the
    user to prove
  + Variable instantiations are optional; they are helpful if some of
    the bound variables in the formula do not appear in its conclusion
  + Similar to `apply`, but works backward instead of forward
* Assert tactic:  `assert <formula>.`
  + Extensibella searches for a proof of the formula; if one is not
    found, the formula is added as a subgoal for the user to prove
  + Once the formula is proven, it is added to the context as a
    hypothesis
* Exists tactic:  `exists <tm>.`
  + When the goal is of the form `exists <var>, <formula>`, replaces
    occurrences of `<var>` with `<tm>`
* Search tactic:  `search <depth>.`
  + Searches for a way to prove the current goal, using rules to the
    given depth
  + If no depth is given, uses the default depth (which may be set as
    an option as discussed below)
* Split tactic:  `split.`
  + Given a goal that is a conjunction, splits it into separate
    subgoals for the right and the left
* Left tactic:  `left.`
  + Given a goal that is a disjunction, chooses to prove the left
    side, discarding the right
* Right tactic:  `right.`
  + Given a goal that is a disjunction, chooses to prove the right
    side, discarding the left

Some of the tactics have specific restrictions not seen in Abella
because we are reasoning in an extensible setting:
* Case tactic:  `case <hyp>.`
  + Analyze the ways in which the formula in hypothesis `<hyp>` might
    have been derived
  + If `<hyp>` has the form `rel t1 ... tn` and `rel` is an extensible
    relation in the language, then
    - Its primary component `ti` must be built by a known constructor
      (not a variable or the explicit unknown constructor, discussed
      [elsewhere](extensibility.md)), or
    - Its primary component can be built by the explicit unknown
      constructor if the relation is introduced by the current
      extension
  + If `<hyp>` is not a built by a relation or the relation is a fixed
    relation, either as part of the language or introduced as a proof
    relation, case analysis has no extra restrictions
* Unfold tactic:  `unfold.`
  + For a goal of the form `rel t1 ... tn`, if there is only one rule
    for the goal that could prove it, replace the goal with the body
    of the rule
  + If `rel` is an extensible relation, its primary component must be
    built by a known constructor, not a variable or the explicit
    unknown constructor

The preceding tactics may be prefaced with a name for Extensibella to
try to use for the hypotheses produced by it.  For example, the tactic
`N: case H1.` will have any hypotheses it produces starting with `N`.

There are also tactics that don't move the proof forward, but may be
useful:
* Skip tactic:  `skip.`
  + Skips the current subgoal, moving to the next one
  + Treats the subgoal as if it were truly solved
* Abort tactic:  `abort.`
  + Aborts proving the current theorem
  + Does not add the theorem to the set of known theorems
* Undo tactic:  `undo.`
  + Undoes the effect of the last tactic
* Clear tactic:  `clear <name>.`
  + Removes the hypothesis with the given name from the context
* Rename tactic:  `rename <name 1> to <name 2>.`
  + Change from one name for something to another


## Common Commands
Command commands may be used either inside or outside of a proof.
* Show command:  `Show <thm>.`
  + Displays a previously-proven theorem
* Quit command:  `Quit.`
  + Exists Extensibella
* Set command:  `Set <option> <value>.`
  + Sets the given option to the given value, if valid
  + Valid options:
    - `search_depth`:  How deep to search when looking for an
      automatic proof.  Value must be an integer.
    - `debug`:  Whether to display the behind-the-scenes interaction
      with Abella.  This is intended only for developing and debugging
      Extensibella itself, and does not provide useful information for
      a proof.  Value must be `on` or `off`.



[1]: http://abella-prover.org/reference-guide.html
