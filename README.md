# Verified Regular Expression Matching (WIP)

## Environment setup
- This project compiles with Coq 8.19.2 and OCaml 5.2.0. We recommend setting up a fresh Opam switch with these versions, and use the [coq-lsp](https://github.com/ejgallego/coq-lsp) VS Code extension (instead of VSCoq). 
- **Note**: if you are using VS Code, please open VS Code in the `coq` subdirectory by `cd`-ing to the `coq` subdirectory and running `code .` in the terminal (this is needed for `coq-lsp` to work properly). 

## Coq code 
The `coq` subdirectory contains Jules' code for verified regex derivatives 
(see [`Regex.v`](./coq/Regex.v)). This file requires installing the `coq-stdpp` library:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp
```
- [`Antimirov.v`](./coq/Antimirov.v): Antimirov derivatives
- [`Brzozowski.v`](./coq/Brzozowski.v): Brzozowski derivatives
- [`Filinski.v`](./coq/Filinski.v): Our attempt at mechanizing the Filinski paper mentioned below

We also referenced the code from the CS 6115 lecture (Fall 2017) on regexes ([link](https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/SimpleLex.html))
 

## OCaml code 
The `ocaml` subdirectory contains executable implementations of regex matchers:
- [`harper.ml`](./ocaml/lib/harper.ml) contains the code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
- [`filinski.ml`](./ocaml/lib/filinski.ml) contains the code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), also translated from SML to OCaml 
- [`antimirov.ml`](./ocaml/lib/antimirov.ml) contains Neel Krishnaswami's implementation of regex matching using Antimirov derivatives ([link](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html))

- Run `opam install ppx_jane base` to install all OCaml dependencies

- Run `dune exec -- main` to see the result of the staged regex matcher (Filinski section 3) on the empty string for matching `ε*`:
```ocaml
Compiled program:
(((true AtEnd) (false (Or (Cont true (CN 0)) (Cont false (CN 2))))
  (true (Cont true (CN 1)))
  (true (Or (Cont true (CN 0)) (Cont false (CN 2)))))
 (CN 3))
result = true
```
