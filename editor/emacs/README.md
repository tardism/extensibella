
This directory holds the Proof General instance for Extensibella.  To
use it, its files need to be copied to a directory named
`extensibella` in the Proof General directory.  You also need to add
the following line to the `generic/proof-site.el` file in the Proof
General directory, in the `proof-assistant-table-default`:
```
(extensibella "Extensibella" "xthm")
```
so it will know to open Extensibella files using this mode
automatically.

