# Verified Regular Expression Matching (WIP)

- [`harper.ml`](./lib/harper.ml) contains the code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
- [`filinski.ml`](./lib/filinski.ml) contains the code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), also translated from SML to OCaml 

- Run `dune exec -- main` to see the result of the staged regex matcher (Filinski section 3) on the empty string for matching `ε*`. 
