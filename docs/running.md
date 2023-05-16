# Running Extensibella
There are several ways to run Extensibella, both interactively and for
processing a full file.  We discuss each below.


## Running a REPL in the Terminal
Extensibella is primarily an interactive proof assistant for reasoning
about extensible languages.  We can run Extensibella in the terminal
as `extensibella`.  This will start a REPL with a basic prompt:
```
 < 
```
The Extensibella commands for loading and reasoning about a language
module can then be entered at this prompt.  A command is read when a
line ending with a period, optionally followed by white space, is
read.  This command is then processed, with the output resulting from
it printed to the terminal followed by a new prompt, waiting for the
next command.

When running Extensibella in the terminal, the `Quit.` command will
exit, as will `Ctrl+D`.


## Running in Proof General
While properties can be proven in Extensibella's REPL directly, the
preferred method of developing proofs is to use Proof General.  [Proof
General](https://proofgeneral.github.io/) is an Emacs mode for
interactive proof assistants.  It allows the user to write a file of
commands and step through them automatically, maintaining a marker for
the current location in the proof file, displaying the proof state in
a separate Emacs window.

Instructions for installing the Extensibella Emacs Proof General
sub-mode can be found in the [Emacs editor
directory](../editor/emacs/README.md).  This has only been tested with
the [Abella version of Proof
General](https://github.com/abella-prover/PG); it will likely work
with other versions, but has not been tested with them.


## Checking a Full File
Finally, once a proof file has been fully developed, we can check the
file as a full unit.  If we have a file `proofs.xthm`, we can check
its contents in the terminal as
```
extensibella --check proofs.xthm
```
This checks all the proofs in the file, only printing out the message
for the check being successful at the end or an error message for what
went wrong in checking it.  The results of commands are not printed.

This mode may also be used to check a number of files at the same time
by listing all the files to process:
```
extensibella --check file_1.xthm ... file_n.xthm
```
Each file is checked individually, separate from the other files.


## Compiling a Full File
Once a file's proofs are fully completed, we compile it so other
modules can build on its properties.  We compile a file `proofs.xthm`
as
```
extensibella --compile proofs.xthm
```
It is assumed the file's proofs are valid when it is compiled, but
this is not checked.  The compilation may crash in some cases where
the file being compiled is not valid in checking.

We can combine the checking and compiling operations at once:
```
extensibella --compile --check proofs.xthm
```
This will check the file is valid before compiling it.

We can also handle multiple files for compilation at once:
```
extensibella --compile file_1.xthm ... file_n.xthm
```
The files will be processed in the order they are given.

Note that if we give a list of files for compilation and checking at
once, the order of the files is important.  If we have files
`host.xthm` and `ext.xthm` for a host language and an extension to it,
checking and compiling them as
```
extensibella --check --compile ext.xthm host.xthm
```
the `ext.xthm` file will be processed first, so it is checked with the
old version (if there is one) of the host's compiled theorem file.
This is likely not what was intended, since any updates to the
`host.xthm` file should be included in checking `ext.xthm` to make
sure it is valid with respect to them.


## Generating a File Skeleton
Each theorem file for an extension must include the correct `Prove`
commands for the theorems from modules on which it builds.  While this
can be built by hand, it is much easier to request Extensibella build
a skeleton of these `Prove` commands:
```
extensibella --generate lang:ext ext.xthm
```
This will produce a file `ext.xthm` with `Prove` commands for each
imported property.  The user can then fill in the proofs, and add any
new properties.

Note that this asks the user before overwriting an existing file.
Since proof files represent a great deal of work, adding a safeguard
for overwriting them seemed a wise precaution.
