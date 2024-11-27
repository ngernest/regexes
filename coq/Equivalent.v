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

Lemma isEmpty_Concat : forall (s1 s2 : string) (r1 r2 : re),
   isEmpty (fold_left b_der s1 r1) ->
   isEmpty (fold_left b_der s2 r2) ->
   isEmpty (fold_left b_der (s1 ++ s2) (Concat r1 r2)).
Proof. 
  induction s1. induction s2.
  - intros. X. 
  - intros. X. rewrite b_der_union. simpl. 
    apply orb_prop_intro. right. apply H0.
  - intros. X. rewrite b_der_union. simpl. 
    apply orb_prop_intro. left. apply IHs1. apply H. apply H0.
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
  - destruct H0. destruct s; simpl in *.
    + exists (Union r1 r2). simpl. split. 
      destruct isEmpty; eauto. destruct isEmpty.
      reflexivity. destruct H. set_solver.
    + rewrite b_der_union in H. simpl in H. destruct isEmpty eqn:E1.
      * assert (Is_true (b_matches r1 (a :: s))) as H1. 
        { unfold b_matches. simpl. rewrite E1. apply I. }
        apply IHr1 in H1. unfold a_matches, nullable in H1. 
        X. exists x. split. apply H. 
        rewrite a_der_set_singleton in *. simpl. 
        rewrite fold_left_union. apply elem_of_union_l.
        apply H0.
      * destruct (isEmpty (fold_left b_der s (b_der r2 a))) eqn:E2. 
        -- assert (Is_true (b_matches r2 (a :: s))) as H1. 
           { unfold b_matches. simpl. rewrite E2. apply I. }
           apply IHr2 in H1. unfold a_matches, nullable in H1. 
           X. exists x. split. apply H. rewrite a_der_set_singleton in *. simpl.
          rewrite fold_left_union. apply elem_of_union_r. apply H0.
        -- inversion H. 
  - assert (a_matches (Concat r1 r2) s).
    { unfold a_matches, nullable. X. }
    apply a_matches_concat in H1. destruct H1 as [s1 [s2 [H1 [H2]]]].
    apply IHr1 in H2. apply IHr2 in H3.
    unfold b_matches in *. X. 
    apply isEmpty_Concat. apply H2. apply H3.
  - destruct H0. assert (b_matches (Concat r1 r2) s).
    { unfold a_matches, nullable. X. }
    apply b_der_concat in H0. destruct H0 as [s1 [s2 [H0 [H1 H2]]]].
    apply IHr1 in H1. apply IHr2 in H2.
    assert (a_matches (Concat r1 r2) (s1 ++ s2)).
    apply a_matches_Concat. apply H1. apply H2.
    unfold a_matches, nullable in H3. X. 
Admitted.
