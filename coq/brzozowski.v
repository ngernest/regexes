Require Import Regex.

(* Brzozowski derivative of a regular expression 
  with respect to a character *)
Fixpoint der (r : re) (a : char) : re :=
  match r with
  | Empty => Empty
  | Epsilon => Empty
  | Atom b => if eq_dec a b then Epsilon else Empty
  | Union r1 r2 => Union (der r1 a) (der r2 a)
  | Concat r1 r2 => 
    if eps r1 
      then Union (Concat (der r1 a) r2) (der r2 a) 
    else Concat (der r1 a) r2
  | Star r => Concat (der r a) (Star r)
  end.

Lemma der_matches_1 a r s : matches (der r a) s -> matches r (a :: s).
Proof. revert s. induction r; X. Qed.

Lemma der_matches_2 a r s : matches r (a :: s) -> matches (der r a) s.
Proof. revert s. induction r; X. apply eps_matches_2 in H2. X. Qed.

Hint Resolve der_matches_1 der_matches_2 : core.

Definition matches' (r : re) (s : string) : bool :=
  eps (fold_left der s r).

Lemma matches'_matches r s : matches' r s = true <-> matches r s.
Proof. unfold matches'. split; revert r; induction s; X. Qed.

(* From Jules:

  This could be extended in various ways:
  - Other logical operators (negation, intersection, xor)
  - Weighted version
  - Antimirov derivatives
  - Apply simplification rules to regexes, prove that derivatives only 
    generate finitely many regexes up to the simplification rules 
    (so that you could build a DFA with it)
*)