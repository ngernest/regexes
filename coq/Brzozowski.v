Require Import Regex.

(* Brzozowski b_derivative of a regular expression 
  with respect to a character *)
Fixpoint b_der (r : re) (a : char) : re :=
  match r with
  | Void => Void
  | Epsilon => Void
  | Atom b => if char_dec a b then Epsilon else Void
  | Union r1 r2 => Union (b_der r1 a) (b_der r2 a)
  | Concat r1 r2 => 
    if isEmpty r1 
      then Union (Concat (b_der r1 a) r2) (b_der r2 a) 
    else Concat (b_der r1 a) r2
  | Star r => Concat (b_der r a) (Star r)
  end.

Lemma b_der_matches_1 a r s : matches (b_der r a) s -> matches r (a :: s).
Proof. revert s. induction r; X. Qed.

Lemma b_der_matches_2 a r s : matches r (a :: s) -> matches (b_der r a) s.
Proof. revert s. induction r; X. apply isEmpty_matches_2 in H2. X. Qed.

Hint Resolve b_der_matches_1 b_der_matches_2 : core.

Definition matches' (r : re) (s : string) : bool :=
  isEmpty (fold_left b_der s r).

Lemma matches'_matches r s : matches' r s = true <-> matches r s.
Proof. unfold matches'. split; revert r; induction s; X. Qed.

(* From Jules:

  This could be extended in various ways:
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
*)
