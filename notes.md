# Things we could do

**Antimirov**:
- continue [Michael Greenberg's investigation](https://www.weaselhat.com/post-819.html) into the size of Brzozowski derivatives, but apply them to Antimirov instead
- given a regex `r`, the number of Antimirov word derivatives is linear in the size of `r` (source)
- Up to similarity, the union of the set of Antimirov partial derivatives of a regular expression and the Brzozowski derivative are the same.
- see https://cstheory.stackexchange.com/questions/41939/time-complexity-of-derivative-based-regex-matchers
- correctness theorems:
    - `forall r s, matches r s <-> antimirov_matches r s = true`
    - `forall r s, antimirov_matches r s = true <-> brzozowski_matches r s = true`
    - the regex sum of all regexes in the Antimirov set is equivalent (up to ACI)
to Brzozowski
- compute a finite automaton
- connect Brzozowski and Antimirov: `B(r) : list re := {fold sum a | a ⊂ A(r)}`.
Antimirov generates finite sets. can sum them together to get Brzozowski.
Finitely many B ders: `forall r, {B_w(r) | w word}` is finite
- rewrite rules: `a + a = a`, `a + b = b + a if a < b`, `a + (b + c) = (a + b) + c`, 
`(a + b) + b -> a + b`, `(a + c) + b -> (a + b) + c`

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

**Ideas from Jules**
- Other logical operators (negation, intersection, xor)
- Weighted version
- Antimirov b_derivatives
- Apply simplification rules to regexes, prove that b_derivatives only 
  generate finitely many regexes up to the simplification rules 
  (so that you could build a DFA with it)

For the extensions I suggested above, here are some challenges you might encounter:
Other logical operators such as negation: how do you reformulate the matches relation? Coq will reject a naive definition due to a non-positive recursive occurrence
Weighted version: it'd be neat to have a version with star semirings, but how do you specify the correctness in that case?
Antimirov derivatives: I think this should be fairly straightforward. It would also work with the weighted version
Simplification rules: some care has to be taken to convince Coq of the termination of the simplification. In order to generate a finite automaton, you'd have to incorporate commutativity & associativity of +. You could also define a representation with an n-ary +, with the list kept in sorted & deduplicated order
In general, it would be neat to have a regex matcher that can be extracted to ocaml code (using Coq's Extraction), and is reasonably efficient
Another extension that would be neat is generating a minimal automaton. Or a compiler that outputs Iris-VST verified C code. But those would be more difficult :slightly_smiling_face:

## Questions for Jules
- Is it possible to write a decision procedure in OCaml and then call that decision procedure in Coq (as part of proof by reflection)?
  - I was thinking of using the OCaml code for using Antimirov derivatives to construct an NFA-based regex matcher (in `antimirov.ml`) and somehow calling the OCaml NFA construction code in Coq, but I wasn't sure how to do this 
- Edelmann mentions that his Zipper-based set representation of Brzozowski derivatives is "reminiscent" of Antimirov derivatives -- is there a way to formalize this intuition in Coq (e.g. what would a lemma stating this connection look like?)



