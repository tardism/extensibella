# Abella Communication
Extensibella uses [Abella](http://abella-prover.org/index.html) in the
back end for checking the logical validity of reasoning, handling only
the extensibility portions of reasoning itself.

When Extensibella starts and the module declaration `Module mo:du:le.`
is read, it
* Starts an Abella process in the background
* Imports the [Extensibella standard library](../stdLib) into the
  Abella process
* Enters the module definition file contents as a series of commands
  into the Abella process.

Once it has done this, it is ready to take commands from the user.

Each Extensibella command corresponds to some sequence of Abella
commands.  When a command is entered,
* Extensibella translates the entered command to Abella's language
* Sends it to Abella
* Reads back Abella's output
* Translates it from Abella's language to Extensibella's language
* Shows it to the user

The translations turn short names into qualified names and vice versa
(e.g. `rel` and `mo:du:le:rel`), as well as moving between the
Extensibella and Abella ways of representing qualified names
(e.g. `mo:du:le:rel` and `mo-$-du-$-le-$-rel`), and turn special
Extensibella syntax and the corresponding Abella relations into each
other (e.g. `a + b = c` and `$plus_integer a b c`).

To view the commands it is sending, the Extensibella command `Set
debug on.` will show all the commands sent to Abella as well as
Abella's response.  Alternatively, running Extensibella with the
`--dump-Abella` flag will output all the Abella commands into a file
`abella_dump.thm` that can be run with Abella.

Most Extensibella commands correspond directly to a single Abella
command, since they have the same meaning.  The commands for
extensible theorems, translation constraints, and extension induction
declarations are the ones with more interesting translations.


## Extensible Theorems
As expected, a declaration of an extensible theorem turns into a
regular theorem declaration plus some other code.  Suppose we have a
declaration
```
Extensible_Theorem thm : forall x y,
    R : r x y -> Q : q x -> s y
  on Q.
```
This turns into a theorem declaration and some set-up code:
```
Theorem thm : forall x y, r x y -> q x -> s y.
induction on 2. intros R Q. Q: case Q (keep).
```
This sets up the induction and case analysis as declared in the
extensible theorem and gives the declared names to the premises.  We
use the `(keep)` flag on the case analysis because we might find it
useful to have the original premise.

If we have two or more mutually-inductive theorems to prove, we have a
similar set-up.  Suppose we have the following:
```
Extensible_Theorem
  thm1 : forall x y,
    R : r x y -> Q : q x -> s y
  on Q,
  thm2 : forall a,
    M : m a -> r a a
  on M.
```
The set-up code creates an Abella mutually-inductive theorem with a
placeholder name for this and sets it up:
```
Theorem $extThm_1 :
  (forall x y, r x y -> q x -> s y) /\
  (forall a, m a -> r a a).
induction on 2 1. split.
  intros R Q. Q: case Q (keep).
```
This sets up the induction for both and splits them so we can prove
each.  The last line then does the set-up for the first theorem
specifically, and the user proves the cases for that theorem.

The set-up for the latter theorem is remembered so we can issue it
when we get there.  Extensibella computes the subgoal number Abella
will use for the second (or any subsequent) theorems when it reaches
them, then looks for this in the Abella output it reads.  Once it
reads the right subgoal number, subgoal 2 in this case, it issues the
set-up code for the second theorem:
```
intros M. M: case M (keep).
```
The user then proves each case for this property.

Once the user has proven all the cases, both theorems are proven.
However, they do not have the names given to them by the user yet.
When the original theorem declaration is given to Abella, it creates a
`Split` command to create the two theorems with the names declared by
the user:
```
Split $extThm_1 as thm1, thm2.
```
It then holds onto this command until the theorem is proven, issuing
it once Abella tells it the proof of the original, combined theorem it
entered is complete.  Then the theorems are both known by the names
the user gave, and ready to be used in further proofs.

### Preservability
The preservability case ends up being mostly built into Extensibella
through the encoding of the language, as described in the [discussion
of the encoding format](encoding_format.md).  It corresponds to the
rule for the explicit unknown constructor, either the copy rule or the
rule standing in for rules introduced by other extensions.

If it is the copy rule, the preservability proof is just to prove it
will hold in the case where that rule is how the relation is defined.
This means the only assumptions we need are those included in the rule
itself, so the proof case is exactly what Abella presents already.

If it is a rule standing in for rules introduced by other extensions,
we need to put in more work.  Recall from the [encoding
format](encoding_format.md) that the stand-in rule has the form
```
rel A <unknown ty> B :=
   exists Trans, (0 = 0 -> false) /\ rel A Trans B
```
where the arguments to the relation are the same other than replacing
the primary component with a variable named `Trans`.  Recall also from
the [discussion of extensibility](extensibility.md) that we need to
have an `Ext_Ind` definition for the relation for this induction to be
valid.  We remove the first assumption, as we don't need it and must
not have it, then assert the translation from the `Ext_Ind` holds,
skipping the proof of it:
```
clear <name>. assert |{ty}- <unknown ty> ~~> Trans. skip.
```
This adds the translation assumption we need for proving
preservability, so the property will hold for an existing derivation
of the relation on the translation.  Note this is also why the exact
name needs to be `Trans`, so we can easily generate this.  This
assertion is generated when the extensible theorem is declared, and is
stored along with the subgoal number for the preservability proof.  As
with the set-up code for a second theorem, this is stored until we
reach the subgoal where it is expected, then it is issued.

### Proving in Further Extensions
A `Prove` command for adding to the proof of a theorem in an
extension, looks up the theorems it is to prove in the set of
obligations imposed on the current module by those it imports.  It
then uses the same set-up code as the original declaration based on
the theorem statements it finds, and adds the same commands to occur
during the Abella proof and after it.

The difference is that it only needs to prove a subset of the existing
cases.  This is accomplished by tracking which module introduced the
rules in the relation definition, then introducing `skip` commands for
each applicable rule the current module need not prove.  The `skip`s
are stored, along with the subgoal numbers to which they apply, as is
done with other commands that need to occur during the proof.


## Translation Constraints
Translation constraints are similar to extensible properties.
However, with a translation constraint, we do not have any induction
to declare, so our set-up only uses `intros` and `case`.  The handling
of proving translation constraints in extensions is done in the same
way as for extensible theorems.


## Extension Induction Declarations
An `Ext_Ind` declaration generates two definitions.  One is the
extension size for the relation, `<r {ES}>`, and the other is the
translation version of the relation, `<r {T}>`.  These are generated
based on the original clauses in the relation as discussed in the
[discussion of Ext_Ind](extensibility.md).

`Prove_Ext_Ind` generates two definitions and a theorem.  The
definitions are the same as for the original `Ext_Ind`, the extension
size and the translation version.  It also generates a theorem `forall
x, <r {ES}> x -> <r {T}> x.` This is an extensible theorem, and the
handling of setting it up and skipping the cases the current module
need not prove is handled as for extensible theorems.
