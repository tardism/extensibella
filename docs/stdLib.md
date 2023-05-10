# Standard Library
Extensibella contains a standard library for working with built-in
types, written in Abella directly.  In addition to defining
Extensibella's built-in datatypes and operations on them, it proves
properties about them that can be used in proofs.

The standard library can be found in the [`stdLib`
directory](../stdLib).  There is currently no good way to view the
theorems it provides.  The only way to do so is to search through the
files looking for anything starting with `extensibella-$-stdLib-$-`;
these will be theorems available for use in Extensibella, with a
theorem proven as `extensibella-$-stdLib-$-thm` having the qualified
name `extensibella:stdLib:thm`.  We plan to produce actual
documentation about the theorems in the standard library that will
update when they update, but that has not happened yet.
