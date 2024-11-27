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

Lemma b_der_void : forall (s : string), fold_left b_der s Void = Void.
Proof. induction s. reflexivity. simpl. apply IHs. Qed.

Lemma b_der_union : forall (s : string) (r1 r2 : re), 
  fold_left b_der s (Union r1 r2) = Union (fold_left b_der s r1) (fold_left b_der s r2).
Proof. 
  induction s. 
  - reflexivity.
  - simpl in *. intros. apply IHs. 
Qed.

Lemma b_der_concat : forall (s : string) (r1 r2 : re),
  b_matches (Concat r1 r2) s ->
  exists s1 s2, (s = s1 ++ s2) /\ b_matches r1 s1 /\ b_matches r2 s2.
Proof. 
  induction s; unfold b_matches in *; X.
  - exists []. exists []. X.
  - rewrite b_der_union in H. simpl in H. 
    destruct (isEmpty (fold_left b_der s (Concat (b_der r1 a) r2))) eqn:E1;
    destruct (isEmpty (fold_left b_der s (b_der r2 a))) eqn:E2; simpl in *.
    + assert (isEmpty (fold_left b_der s (Concat (b_der r1 a) r2))) by X.
      apply IHs in H0. destruct H0 as [s1 [s2 [H0 [H1 H2]]]].
      exists (a :: s1). exists s2. repeat split; X.
    + assert (isEmpty (fold_left b_der s (Concat (b_der r1 a) r2))) by X.
      apply IHs in H0. destruct H0 as [s1 [s2 [H0 [H1 H2]]]].
      exists (a :: s1). exists s2. repeat split; X.
    + assert (isEmpty (fold_left b_der s (b_der r2 a))) by X.
      exists []. exists (a :: s). repeat split; X.
    + destruct H.
  - apply IHs in H. destruct H as [s1 [s2 [H0 [H1 H2]]]].
    exists (a :: s1). exists s2. repeat split; X.
Qed.

