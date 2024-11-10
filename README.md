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
- [`ReCountable.v`](./coq/ReCountable.v): Proving that regexes are countable
- [`Regex_opt.v`](./coq/Regex_opt.v): Smart constructors for regexes
- [`ListMonad.v`](./coq/ListMonad.v) : The list monad
- [`Filinski.v`](./coq/Filinski.v): Our attempt at mechanizing the Filinski paper mentioned below

We also referenced the code from the CS 6115 lecture (Fall 2017) on regexes ([link](https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/SimpleLex.html))
 

## OCaml code 
The `ocaml` subdirectory contains executable implementations of regex matchers:
- [`harper.ml`](./ocaml/lib/harper.ml) contains the code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
- [`filinski.ml`](./ocaml/lib/filinski.ml) contains the code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), also translated from SML to OCaml 
- [`antimirov.ml`](./ocaml/lib/antimirov.ml) contains Neel Krishnaswami's implementation of regex matching using Antimirov derivatives ([link](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html)), along with some experiments using QuickCheck to test lemmas regarding Antimirov derivatives 
- [`zipper.ml`](./ocaml/lib/zipper.ml) contains an implementation of [Huet's zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)) (adapted from chapter 2.3 of [Romain Edelmann's PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content))     
- [`brzozowski_zipper.ml`](./ocaml/lib/brzozowski_zipper.ml) contains an implementation of Brozozwski derivatives via zippers (adapted from chapter 2.6 of [Edelmann's dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content))     

### Building the OCaml code
- Run `opam install ppx_jane base base_quickcheck sexplib stdio ppx_quick_test` to install all OCaml dependencies
- Run `dune runtest` to run some QuickCheck tests regarding Antimirov derivatives (see [`antimirov.ml`](./ocaml/lib/antimirov.ml) 
- Run `dune exec -- main` to see how QuickCheck falsifies the property that Brzozowski derivatives are always contained within the set of Antimirov derivatives (when the set is non-empty)