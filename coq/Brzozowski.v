Require Export Regex.

(** Brzozowski derivative of a regex with respect to a character *)
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

(** True if r matches s, using b_der *)
Definition b_matches (r : re) (s : string) : bool :=
  isEmpty (fold_left b_der s r).

Lemma b_matches_matches r s : b_matches r s = true <-> matches r s.
Proof. unfold b_matches. split; revert r; induction s; X. Qed.
