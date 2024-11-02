# Verified Regular Expression Matching (WIP)

## Coq code 
The `coq` subdirectory contains Jules' code for verified regex derivatives 
(see [`jules_regex_derivatives.v`](./coq/jules_regex_derivatives.v)). This file requires installing the `coq-stdpp` library:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp
```

## OCaml code 
The `ocaml` subdirectory contains executable implementations of regex matchers:
- [`harper.ml`](./ocaml/lib/harper.ml) contains the code from "Proof-directed debugging" (Harper 1998), translated from SML to OCaml
- [`filinski.ml`](./ocaml/lib/filinski.ml) contains the code from "Proof-directed program transformation: A functional account of efficient regular expression matching" (Filinski 2021), also translated from SML to OCaml 

- Run `dune exec -- main` to see the result of the staged regex matcher (Filinski section 3) on the empty string for matching `ε*`. 

```ocaml
Compiled program:
(((true AtEnd) (false (Or (Cont true (CN 0)) (Cont false (CN 2))))
  (true (Cont true (CN 1)))
  (true (Or (Cont true (CN 0)) (Cont false (CN 2)))))
 (CN 3))
result = true
```