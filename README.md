# Extensibella
Extensibella is a system for proving properties about extensible
languages in a modular fashion, with a guarantee that the proven
theorems will hold in any composed language.


## Extensible Languages
There are several views of extensible languages in the literature.
The view we use is one with a base language and
independently-developed extensions to this base, and guaranteed
composition of the base language and extensions.

The base language introduces a set of syntactic categories and
constructors building them.  It also introduces a set of semantic
analyses.

Extensions can add new constructors building the syntactic categories
from the base language and define the base language's semantic
analyses on them.  Any such new constructors are also given a
translation to the base language.  Extensions can also introduce new
syntactic categories and constructors of them, as well as new semantic
analyses.  When we combine multiple extensions, these new analyses are
defined on constructors from other extensions by using the definition
on the translation.


## Language Encodings
Extensibella uses encodings of extensible languages into
[Abella](https://abella-prover.org/index.html) for reasoning.  An example
language is found in the `exampleEncoding/` directory along with an
Extensibella proof script proving a few properties about it.

Languages written in
[SOS-Ext](https://github.com/RandomActsOfGrammar/extensibella) can be encoded
into Extensibella using the `--extensibella` flag.  These encoded
languages will be found by Extensibella automatically.

We plan to implement an encoding to Extensibella for a restricted
subset of [Silver](https://github.com/melt-umn/silver) grammars as well.  Once
implemented, these encoded languages will also be found by
Extensibella automatically.

Encodings for other systems can also be written following the example
of the language in the `exampleEncoding/` directory and the
documentation in the `docs/encoding_format.md` document.  The
generated locations for these can be added to Extensibella by setting
the `EXTENSIBELLA_ENCODED` environment variable before running the
`extensibella` command.


## Required Software and Set-Up
Extensibella is written in [Silver](https://github.com/melt-umn/silver) and
thus requires Silver for building.  Extensibella uses the [Abella
Proof Assistant](https://abella-prover.org/index.html) as a logical back-end
for handling proof aspects other than extensibility.  Running
Extensibella requires Java 8, Bash, and Abella.

Once this software is installed, run
```
./build
```
in the repository root to build the Extensibella system using Silver.
Then run
```
./install
```
to install the `extensibella` script.  Extensibella can then be run as
`extensibella`.

Extensibella has been tested on Linux, but may run on MacOS or the
Windows Subsystem for Linux (WSL).


## Documentation
Documentation for writing language encodings and proving properties
about them in Extensibella can be found in the [docs
directory](docs/).

Additionally the [example encoding directory](exampleEncoding/)
contains an example encoding and proofs of a few properties about it.

Finally, the [SOS-Ext
repository](https://github.com/RandomActsOfGrammar/sos-ext) contains
several example SOS-Ext languages, some of which have Extensibella
proofs of their properties.  Of particular note is the
[`sec_SOS`](https://github.com/RandomActsOfGrammar/sos-ext/tree/master/examples/sec_SOS)
language.
