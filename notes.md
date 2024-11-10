# Things we could do

**Antimirov**:
- continue [Michael Greenberg's investigation](https://www.weaselhat.com/post-819.html) into the size of Brzozowski derivatives, but apply them to Antimirov instead
- given a regex `r`, the number of Antimirov word derivatives is linear in the size of `r` (source)
- Up to similarity, the union of the set of Antimirov partial derivatives of a regular expression and the Brzozowski derivative are the same.
- see https://cstheory.stackexchange.com/questions/41939/time-complexity-of-derivative-based-regex-matchers

**Zippers**
- In his [PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content), Romain Edelmann proves that Brzozowski derivatives are finite by representing them as zippers (he also has a [Coq development here](https://github.com/epfl-lara/silex-proofs/tree/master))
  - ^^ perhaps this is another way to prove that Brzozowski is finite?
- Edelmann mentions that his set-based representation of zippers is reminiscent of Antimirov:
> The zipper-based representation provides a way to effectively classify expressions
and their derivatives into a finite number of equivalence classes, in a manner that is
reminiscent of the partial derivatives of Antimirov. (pg. 7)

> Focuses follow the
recursive structure of Brzozowski’s derivation operation, splitting into multiple focuses in
case multiple recursive calls are made. As a result of following the structure of derivation,
focal points will not appear at arbitrary points within regular expressions. Intuitively, focuses
will always be on points located at the front of expressions. Indeed, derivation is only ever
recursively called on subexpressions semantically located at the front of the expression. For
this reason, there will not be any expressions to the left of the focal points. Contexts will
represent left-most paths within the expression, and zippers will represent sets of such contexts.
This set-based representation is reminiscent of the partial derivatives of Antimirov. (pg. 23)

## Questions for Jules
- Is it possible to write a decision procedure in OCaml and then call that decision procedure in Coq (as part of proof by reflection)?
  - I was thinking of using the OCaml code for using Antimirov derivatives to construct an NFA-based regex matcher (in `antimirov.ml`) and somehow calling the OCaml NFA construction code in Coq, but I wasn't sure how to do this 




