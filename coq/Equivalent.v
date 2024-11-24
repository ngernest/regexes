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
    destruct s; simpl in *; destruct H1. 
    + exists x; split; eauto.
      apply elem_of_singleton_1 in H0. apply H0. 
    + autorewrite with core in *. inversion H0.
  - rewrite b_der_void in H. simpl in H. apply H.
  - destruct s; simpl in *; eauto.
    rewrite a_der_set_eps in H0. rewrite fold_left_empty in H0. 
    inversion H0.
  - destruct s. 
    + destruct H0. exists Epsilon. 
      simpl. split; [eauto|set_solver]. 
    + simpl in *. rewrite b_der_void in H. apply H. 
  - destruct s; simpl in *. 
    + replace x with (Atom c) in H by set_solver. inversion H. 
    + destruct char_dec. 
      * subst. rewrite a_der_set_atom in H0. 
        destruct s; eauto.
        simpl in *. rewrite a_der_set_eps in H0. 
        rewrite fold_left_empty in H0. inversion H0. 
      * rewrite a_der_set_atom' in H0. rewrite fold_left_empty in H0.
        inversion H0. apply n. 
  - destruct H0. destruct s; simpl in *. 
    + destruct H. 
    + destruct char_dec. 
      * subst. rewrite a_der_set_atom. destruct s; simpl in *. 
        ++ exists Epsilon. split; [eauto|set_solver]. 
        ++ rewrite b_der_void in H. inversion H.
      * rewrite b_der_void in H. inversion H.
  - rewrite b_der_union. simpl.
    destruct s; simpl in *.
    + replace x with (Union r1 r2) in H by set_solver. 
      simpl in H. 
      apply symmetry in H. apply orb_true_elim in H. 
      destruct H; eauto. 
    + rewrite a_der_set_Union in H0. 
      rewrite fold_left_union in H0. apply elem_of_union in H0. 
      destruct H0. 
      * rewrite a_der_set_singleton in H0. apply orb_prop_intro. 
        left. specialize IHr1 with (a :: s). apply IHr1. 
        unfold a_matches. simpl. rewrite a_der_set_singleton.
        unfold nullable. X. 
      * rewrite a_der_set_singleton in H0. apply orb_prop_intro. 
        right. specialize IHr2 with (a :: s). apply IHr2. 
        unfold a_matches. simpl. rewrite a_der_set_singleton.
        unfold nullable. X. 
  - destruct H0. induction s; simpl in *. 
    + exists (Union r1 r2). simpl. split. 
      destruct isEmpty; eauto. destruct isEmpty.
      reflexivity. destruct H. set_solver.
    + rewrite b_der_union in H. simpl in H. destruct isEmpty;
      destruct isEmpty; simpl in *. 
Admitted.
