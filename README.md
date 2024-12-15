# Verified Derivative-Based Regular Expression Matching

This repository contains our work mechanizing proofs related to Brzozowski & Antimirov derivatives. There are two subdirectories: [`coq`](./coq/) & [`ocaml`](./ocaml/), which contain Coq and OCaml code respectively. 

## Coq Environment Setup

### Creating a new Opam switch
This project compiles with Coq 8.19.2 and OCaml 5.2.0. We recommend setting up a fresh Opam switch with these versions:
```bash
opam switch create [switch-name] ocaml-base-compiler.5.2.0
eval $(opam env)
opam pin add coq 8.19.2
```

### Installing the `std++` library
Our Coq code uses the [`coq-std++`](https://gitlab.mpi-sws.org/iris/stdpp) library, which can be installed as follows:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp
```

### Compiling and viewing our code
- To compile: `cd` into the [`coq`](./coq/) subdirectory & run `make` / `make clean` as appropriate. 
- We recommend viewing our Coq code in VS Code using the [coq-lsp](https://github.com/ejgallego/coq-lsp) VS Code extension (instead of VSCoq).
- **Note**: if you are using VS Code, please open VS Code in the `coq` subdirectory by `cd`-ing to the `coq` subdirectory and running `code .` in the terminal (this is needed for `coq-lsp` to work properly).

## Coq code 
- [`Regex.v`](./coq/Regex.v): Definitions related to regular expressions (adapted from Jules)
- [`Antimirov.v`](./coq/Antimirov.v): Antimirov derivatives
- [`Brzozowski.v`](./coq/Brzozowski.v): Brzozowski derivatives
- [`Equivalent.v`](./coq/Equivalent.v): Proof that Antimirov and Brzozowski matchers are equivalent
- [`Finite.v`](./coq/Finite.v): Proof that there are finitely many Antimirov partial derivatives of a regex 
- [`Height.v`](./coq/Height.v): Proofs that height and size of Antimirov derivatives are bounded
- [`EdelmannGset.v`](./coq/EdelmannGset.v): Romain Edelmann's Coq formalization of the zipper representation of Brzozowski derivatives,
  modified to use `gset`s
- [`ZipperAntimirovGset.v`](./coq/ZipperAntimirovGset.v): Proof that the underlying sets of regexes for zippers and Antimirov derivatives are equivalent
 
## OCaml Code 
The `ocaml` subdirectory contains executable implementations of regex matchers:
- [`regex.ml`](./ocaml/lib/regex.ml): Regex definitions + smart constructors + helper functions (e.g. for computing regex size)
- [`brzozowski.ml`](./ocaml/lib/brzozowski.ml): a regex matcher that uses Brzozowski derivatives
- [`antimirov.ml`](./ocaml/lib/antimirov.ml): a regex matcher that uses Antimirov derivatives  
- [`zipper.ml`](./ocaml/lib/zipper.ml) contains an implementation of [Huet's zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)) (adapted from chapter 2.3 of [Romain Edelmann's PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content))     
- [`extracted_brzozowski_zipper.ml`](./ocaml/lib/extracted_brzozowski_zipper.ml): the Coq code from [`Edelmann.v`](./coq/Edelmann.v), extracted to OCaml 
- [`quickcheck_properties.ml`](./ocaml/lib/quickcheck_properties.ml): QuickCheck properties regarding Antimirov / Brzozowski derivatives (which we used to figure out whether lemma statements were valid before proving them)     

### Building & Testing the OCaml Code
First, `cd` into the `ocaml` subdirectory. Then: 
- Run `make install` to install all OCaml dependencies
- Run `make` to build the OCaml code
- (Optional) Run `make test` to run some QuickCheck tests regarding Antimirov derivatives (see [`antimirov.ml`](./ocaml/lib/antimirov.ml)) 
- (Optional) Run `dune exec -- main` to see how QuickCheck falsifies the property that Brzozowski derivatives are always contained within the set of Antimirov derivatives (when the set is non-empty)

### Deprecated (outdated) project work
- [`brzozowski_zipper.ml`](./ocaml/old/brzozowski_zipper.ml): An implementation of Brzozowski derivatives via zippers (translated from the Scala code in chapter 2.6 of [Edelmann's dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content)) 
  - Note: We found out (via QuickCheck tests) that this file is buggy, possibly because we manually translated Edelmann's Scala code to OCaml. This file has been superceded by [`extracted_brzozowski_zipper.ml`](./ocaml/lib/extracted_brzozowski_zipper.ml). 
- [`krishnaswami.ml`](./ocaml/old/krishnaswami.ml): Builds a DFA corresponding to a regex using Antimirov derivatives (adapted from [Neel Krishnaswami's blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html))
- [`ListMonad.v`](./coq/old/ListMonad.v): The list monad (currently unused in the rest of our Coq development)
- [`RegexOpt.v`](./coq/old/RegexOpt.v): Smart constructors for regexes
- [`Edelmann.v`](./coq/old/Edelmann.v): Edelmann's code, using lists instead of `gset`s
- [`ZipperAntimirov.v`](./coq/old/ZipperAntimirov.v): First attempt at proof that underlying sets for zippers and Antimirov derivatives are equivalent 
- We previously tried to mechanize Filinski's JFP 2021 paper "Proof-directed program transformation: A functional account of efficient regular expression matching," but we decided to switch to work on Brzozowski/Antimirov derivatives instead. Our (previous) work involving the Filinski paper is contained in the following files:
  - [`harper.ml`](./ocaml/old/harper.ml): the code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
  - [`filinski.ml`](./ocaml/old/filinski.ml): the code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), translated from SML to OCaml 
  - [`Filinski.v`](./coq/old/Filinski.v): Our (abandoned) attempt at mechanizing the Filinski paper 
  
