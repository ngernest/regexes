From stdpp Require Import gmap sets fin_sets.
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

Lemma b_der_matches_1 (c : char) (r : re) (s : string) : 
  matches (b_der r c) s -> matches r (c :: s).
Proof. revert s. induction r; X. Qed.

Lemma b_der_matches_2 (c : char) (r : re) (s : string) : 
  matches r (c :: s) -> matches (b_der r c) s.
Proof. revert s. induction r; X. apply isEmpty_matches_2 in H2. X. Qed.
Hint Resolve b_der_matches_1 b_der_matches_2 : core.

Definition b_der_str (r : re) (s : string) := fold_left b_der s r.

(** True if r matches s, using b_der *)
Definition b_matches (r : re) (s : string) : bool :=
  isEmpty (fold_left b_der s r).

(* Brzozowski-based matcher agrees with the inductive proposition [matches] *)
Lemma b_matches_matches (r : re) (s : string) : 
  b_matches r s = true <-> matches r s.
Proof. unfold b_matches. split; revert r; induction s; X. Qed.

Lemma b_der_Void : forall (s : string), fold_left b_der s Void = Void.
Proof. induction s. reflexivity. simpl. apply IHs. Qed.

Lemma b_der_Union : forall (s : string) (r1 r2 : re), 
  fold_left b_der s (Union r1 r2) = Union (fold_left b_der s r1) (fold_left b_der s r2).
Proof. 
  induction s. 
  - reflexivity.
  - simpl in *. intros. apply IHs. 
Qed.

Lemma b_matches_Concat : forall (s : string) (r1 r2 : re),
  b_matches (Concat r1 r2) s ->
  exists s1 s2, (s = s1 ++ s2) /\ b_matches r1 s1 /\ b_matches r2 s2.
Proof. 
  induction s; unfold b_matches in *; X.
  - exists []. exists []. X.
  - rewrite b_der_Union in H. simpl in H. 
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

Lemma b_matches_Star : forall (s : string) (r : re),
  s ≠ [] -> b_matches (Star r) s ->
  exists s1 s2, (s = s1 ++ s2) /\ b_matches r s1 /\ b_matches (Star r) s2.
Proof. 
  induction s; unfold b_matches in *; X.
  assert (b_matches (Concat r (Star r)) (a :: s)).
  { unfold b_matches. X. rewrite b_der_Union. X. }
  apply b_matches_Concat in H1. destruct H1 as [s1 [s2 [H1 [H2 H3]]]].
  exists s1. exists s2. X. 
Qed.

Lemma isEmpty_Concat : forall (s1 s2 : string) (r1 r2 : re),
   isEmpty (fold_left b_der s1 r1) ->
   isEmpty (fold_left b_der s2 r2) ->
   isEmpty (fold_left b_der (s1 ++ s2) (Concat r1 r2)).
Proof. 
  induction s1. induction s2.
  - intros. X. 
  - intros. X. rewrite b_der_Union. simpl. 
    apply orb_prop_intro. right. apply H0.
  - intros. X. rewrite b_der_Union. simpl. 
    apply orb_prop_intro. left. apply IHs1. apply H. apply H0.
Qed.

Lemma isEmpty_Star : forall (s1 s2 : string) (r : re),
   isEmpty (fold_left b_der s1 r) ->
   isEmpty (fold_left b_der s2 (Star r)) ->
   isEmpty (fold_left b_der (s1 ++ s2) (Star r)).
Proof. 
  induction s1. induction s2; X.
  X. apply isEmpty_Concat. apply H. apply H0. 
Qed.

(* If [s ~= ε], then [s = ε] *)
Lemma b_matches_Epsilon : forall (s : string),
  b_matches Epsilon s -> s = [].
Proof. 
  destruct s. X. unfold b_matches. simpl. intros. 
  rewrite  b_der_Void in H. contradiction H. 
Qed.

(* If [s ~= r*], then [s ~= r^n] for some [n] *)
Lemma b_matches_Star_Concat : forall (r : re) (s : string),
  b_matches (Star r) s -> 
  exists n, b_matches (Concat_n n r) s.
Proof. 
  induction s using strong_induction.
  intros. destruct n.
  - exists 0. X. 
  - unfold b_matches in H0. simpl in H0. 
    assert (b_matches (Concat (b_der r a) (Star r)) n).
    { unfold b_matches. X. }
    apply b_matches_Concat in H1. 
    destruct H1 as [s1 [s2 [H1 [H2 H3]]]].
    assert (exists n0, b_matches (Concat_n n0 r) s2).
    { apply H. rewrite H1. simpl. rewrite app_length. lia. apply H3. }
    destruct H4. exists (S x).
    unfold b_matches in *. X. rewrite b_der_Union. simpl. 
    apply orb_prop_intro. left. 
    apply isEmpty_Concat. apply H2. apply H4.
    apply isEmpty_Concat. apply H2. apply H4.
Qed.
