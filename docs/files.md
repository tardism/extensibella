
There are five files for each module used with Extensibella.  They are
the definition file, the interface file, the theorem file, the
outerface file, and the full language definition file.  We discuss
each in turn.

Throughout we will mention the `EXTENSIBELLA_ENCODED` set of
directories.  This is an environment variable listing the directories
where special Extensibella files (i.e. every file other than the
theorem file) may be found.  It defaults to
including the Sterling and Extensibella `generated` directories, but
other directories may be added by setting the variable before running
Extensibella.




Definition File
======================================================================
The definition file defines the language syntax and relations.
Extensibella reads this file to learn what the language is.  Its
format is discussed in detail in [encoding_format.md]().

The definition file should be placed in a directory in
`EXTENSIBELLA_ENCODED`.  For a module `mo:du:le`, the definition file
should be named `mo:du:le___definition.thm` (using the standard Abella
file extension).

This is generally expected to be generated as an encoding of a
language written in a system for defining an extensible language
rather than being handwritten.




Interface File
======================================================================
The interface file is a simple list of the modules imported by a
module along with the modules on which they build.  If module
`mo:du:le` imports modules `mod:a` and `mod:b` and `mod:b` build on
`mod:a`, its interface file will be this:
```
mod:b [mod:a]
mod:a []
```
Extensibella reads this file to learn which outerface specifications,
read from the outerface files discussed below, it must fulfill, as
well as how the modules related to one another.  Modules are expected
to be ordered so each module one builds on occurs after it
(e.g. `mod:a` is after `mod:b` in the listing above because `mod:b`
builds on `mod:a`).

The interface file should be placed in a directory in
`EXTENSIBELLA_ENCODED`, generally but not necessarily in the same
directory as the definition file.  For a module `mo:du:le`, the
interface file should be named `mo:du:le___interface.xthmi`.

As with the definition file, this is generally expected to be
generated as part of the encoding of a language written in another
system rather than being written by hand.




Theorem File
======================================================================
The theorem file contains the Extensibella code for declaring and
proving properties.  This is the only file expected to be written by
hand, and is the only one a user of Extensibella should generally need
to concern himself with understanding.  Users do not need to know the
other files exist, beyond a notion of needing to compile things before
writing a theorem file.

The theorem file can be located anywhere.  It can also be given any
name, but should generally have the `.xthm` file extension.




Outerface File
======================================================================
The outerface file contains the theorems and definitions from a
theorem file for a module, but not the proofs.  The outerface can be
thought of as a specification of the extensible theorems for which an
importing module must provide partial proofs and the supporting
non-extensible theorems and definitions to do so.

This file is placed in a directory in `EXTENSIBELLA_ENCODED`.  Having
the outerface lets us have the theorem file itself placed anywhere
while still being able to get the relevant information from it for the
importing modules.  It also includes tags for ordering properties,
these tags being generated in the compilation process, so users do not
need to concern themselves with writing tags.  The outerface file for
module `mo:du:le` is expected to have the name
`mo:du:le___outerface.xthmo`.

The outerface file is expected to be written by compiling a theorem
file using the `--compile` flag with Extensibella.




Full Language Definition File
======================================================================
The full language definition file is used for building composed
proofs.  It is similar to the definition file discussed earlier.  As
with the basic definition file, it includes the definitions of the
language syntax and relations; unlike the basic definition file, it
does not include generic constructors and has separate definitions
giving stand-in rules for various relations.  The details of this
encoding are discussed in [encoding_format.md]().

The full language definition file should be placed in a directory in
`EXTENSIBELLA_ENCODED`.  For a module `mo:du:le`, the definition file
should be named `mo:du:le___full.thm` (using the standard Abella file
extension).

As with the basic definition file, this is generally expected to be
generated from a language description written in a system for defining
an extension language rather than being handwritten.
