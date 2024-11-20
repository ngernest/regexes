Require Import Antimirov.
Require Import Brzozowski.

(** Proofs that Antimirov and Brzozowski derivatives are equivalent *)
Lemma nullable_singleton : forall (r : re), 
  isEmpty r <-> nullable {[ r ]}.
Proof. 
  unfold nullable; induction r; X. 
  - destruct H. exists Epsilon. eauto. 
  - destruct H4. exists (Union r1 r2). simpl. 
    split. 
    + rewrite Heqb. rewrite orb_true_l. reflexivity. 
    + reflexivity.
  - destruct H5. exists (Union r1 r2). split; eauto.
    simpl. rewrite <- H. rewrite orb_true_r. reflexivity.
  - destruct H5. exists (Union r1 r2). split; eauto.
    simpl. rewrite Heqb. rewrite orb_true_l. reflexivity.
  - destruct H4. exists (Concat r1 r2). split; eauto.
    simpl. rewrite Heqb, H. apply eq_sym. apply andb_diag.
  - destruct H1. exists (Star r). split; eauto.
  - destruct H2. exists (Star r). split; eauto.
Qed.

Theorem a_b_matches : forall (r : re) (s : string),
  a_matches r s <-> b_matches r s.
Proof. 
  induction r; unfold a_matches, b_matches, nullable; X.
  - rewrite nullable_singleton. unfold nullable in *. X. 
    destruct s; simpl in *; destruct H1. exists x; split; eauto.
    + apply elem_of_singleton_1 in H0. apply H0. 
    + autorewrite with core in *. inversion H0.
Admitted.
