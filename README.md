# Verified Derivative-Based Regular Expression Matching

This repository contains our work mechanizing proofs related to Brzozowski & Antimirov derivatives. There are two subdirectories: [`coq`](./coq/) & [`ocaml`](./ocaml/), which contain Coq and OCaml code respectively. Instructions on running the demo executables are in the [demo](#demo) section.

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

## Coq Code 
- [`Regex.v`](./coq/Regex.v): Definitions related to regular expressions (adapted from Jules)
- [`Antimirov.v`](./coq/Antimirov.v): Antimirov derivatives
- [`Brzozowski.v`](./coq/Brzozowski.v): Brzozowski derivatives
- [`Equivalent.v`](./coq/Equivalent.v): Proof that Antimirov and Brzozowski matchers are equivalent
- [`Finite.v`](./coq/Finite.v): Proof that there are finitely many Antimirov partial derivatives of a regex 
- [`Height.v`](./coq/Height.v): Proofs that height and size of Antimirov derivatives are bounded
- [`Edelmann.v`](./coq/Edelmann.v): Romain Edelmann's Coq formalization of the zipper representation of Brzozowski derivatives,
  modified to use `gset`s
- [`ZipperAntimirov.v`](./coq/ZipperAntimirov.v): Proof that the underlying sets of regexes for zippers and Antimirov derivatives are equivalent
 
## OCaml Code 
The `ocaml` subdirectory contains executable implementations of regex matchers:
- [`regex.ml`](./ocaml/lib/regex.ml): Regex definitions, smart constructors, and functions for computing regex height and size
- [`brzozowski.ml`](./ocaml/lib/brzozowski.ml): Brzozowski derivative-based regex matcher
- [`antimirov.ml`](./ocaml/lib/antimirov.ml): Antimirov derivative-based regex matcher
- [`zipper.ml`](./ocaml/lib/zipper.ml): An implementation of [Huet's zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)) (adapted from chapter 2.3 of [Romain Edelmann's PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content))     
- [`extracted_brzozowski_zipper.ml`](./ocaml/lib/extracted_brzozowski_zipper.ml): the zipper representation of Brzozowski derivatives, due to Romain Edelmann (extracted from the Coq code in [`EdelmannOriginal.v`](./coq/old/EdelmannOriginal.v))
- [`quickcheck_properties.ml`](./ocaml/lib/quickcheck_properties.ml): QuickCheck random generators and properties regarding derivatives
- [`utils.ml`](./ocaml/lib/utils.ml): Pretty-printers for regexes, other miscellaneous utils
- [`zipper_antimirov.ml`](./ocaml/lib/zipper_antimirov.ml): Demo illustrating that zippers and Antimirov derivatives represent the same set of regexes
- [`three_matchers.ml`](./ocaml/lib/three_matchers.ml): Demo illustrating that the three matchers (Brzozowski, Antimirov, zippers) behave the same
given the same inputs

### Building & Testing the OCaml Code
First, `cd` into the `ocaml` subdirectory. Then: 
- Run `make install` to install all OCaml dependencies
- Run `make` to build the OCaml code
- (Optional) Run `make test` to run our QuickCheck test suite

## Demo 
We have two demo executables:       
- `make demo1`: Generates 15 random (regex, string) pairs and shows that the three regex 
  matchers based on Brzozowski/Antimirov/zippers return the same acceptance result      
- `make demo2`: Generates 15 random (regex, char) pairs and shows that the underlying
  regex sets for both Antimirov derivatives and zippers are the same
  
(Note: we use QuickCheck to generate the random inputs. For reproducibility, we force QuickCheck to use the same seed across different invocations of the executable.)

## Deprecated (outdated) project work
- [`brzozowski_zipper.ml`](./ocaml/old/brzozowski_zipper.ml): An implementation of Brzozowski derivatives via zippers (translated from the Scala code in chapter 2.6 of [Edelmann's dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content)) 
  - Note: We found out (via QuickCheck tests) that this file is buggy, possibly because we manually translated Edelmann's Scala code to OCaml. This file has been superceded by [`extracted_brzozowski_zipper.ml`](./ocaml/lib/extracted_brzozowski_zipper.ml)
- [`krishnaswami.ml`](./ocaml/old/krishnaswami.ml): Builds a DFA corresponding to a regex using Antimirov derivatives (adapted from [Neel Krishnaswami's blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html))
- [`ListMonad.v`](./coq/old/ListMonad.v): The list monad (currently unused in the rest of our Coq development)
- [`RegexOpt.v`](./coq/old/RegexOpt.v): Smart constructors for regexes
- [`EdelmannOriginal.v`](./coq/old/EdelmannOriginal.v): Edelmann's code, using lists instead of `gset`s
- [`ZipperAntimirovOriginal.v`](./coq/old/ZipperAntimirovOriginal.v): First attempt at proof that underlying sets for zippers and Antimirov derivatives are equivalent 
- We previously tried to mechanize Filinski's JFP 2021 paper "Proof-directed program transformation: A functional account of efficient regular expression matching," but we decided to switch to work on Brzozowski/Antimirov derivatives instead. Our (previous) work involving the Filinski paper is contained in the following files:
  - [`harper.ml`](./ocaml/old/harper.ml): The code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
  - [`filinski.ml`](./ocaml/old/filinski.ml): The code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), translated from SML to OCaml 
  - [`Filinski.v`](./coq/old/Filinski.v): Our (abandoned) attempt at mechanizing the Filinski paper 
  