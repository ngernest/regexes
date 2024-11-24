Require Import Antimirov.
Require Import Brzozowski.

(** Examining the height of Antimirov derivatives 
    Inspired by https://www.weaselhat.com/post-819.html *)

(** Computes the size of a regex (no. of AST nodes) *)
Fixpoint re_size (r : re) : nat :=
  match r with
  | Void => 0
  | Epsilon => 1
  | Atom _ => 1
  | Concat re1 re2 => 1 + re_size re1 + re_size re2
  | Union re1 re2 => 1 + re_size re1 + re_size re2
  | Star re' => 1 + re_size re'
  end.

(** Computes the height of a regex 
    (height of the binary tree formed by the AST) *)
Fixpoint re_height (r : re) : nat :=
  match r with
  | Void => 0
  | Epsilon => 1
  | Atom _ => 1
  | Concat re1 re2 => 1 + max (re_height re1) (re_height re2)
  | Union re1 re2 => 1 + max (re_height re1) (re_height re2)
  | Star re' => 1 + re_height re'
  end.

(** Computes the maximum height of a set of regexes *)
Definition max_height_re_set (rs : gset re) : nat := 
  set_fold (fun r acc => max (re_height r) acc) 0 rs.

(** The max height over a union of two sets is just the max height of each 
    of the constituent subsets *)
Lemma max_height_union (s1 s2 : gset re) :
  max_height_re_set (s1 ∪ s2) = max (max_height_re_set s1) (max_height_re_set s2).
Proof.
  Admitted. (* TODO *)

(** Empty set has [max_height = 0] *)
Lemma max_height_empty_set : 
  max_height_re_set gset_empty = 0. 
Proof.
  unfold max_height_re_set.
  apply set_fold_empty.
Qed.

Lemma gset_elements_singleton {A : Type} `{Countable A} (x : A) :
  gset_elements (gset_singleton x) = [x].
Proof.
  unfold gset_elements. simpl. 
  rewrite map_to_list_singleton. reflexivity.
Qed.

(** Folding a function [f] over a singleton set is just the same as applying 
    [f] to the element in the set, along with the base case *)
Lemma set_fold_singleton (f : re -> nat -> nat) (b : nat) (r : re) :
  set_fold f b (gset_singleton r) = f r b.
Proof.
  unfold set_fold, elements; simpl.
  rewrite gset_elements_singleton.
  simpl. reflexivity.
Qed.  

(** Mapping a function [f] over a singleton set returns a singleton 
    set containing the result [f x].  *)
Lemma set_map_singleton (f : re -> re) (x : re):
  set_map f ({[ x ]} : gset re) = ({[ f x ]} : gset re).
Proof.
  unfold set_map, elements.
  replace {[ x ]} with (gset_singleton x) by set_solver.
  rewrite gset_elements_singleton.
  simpl.
  set_solver.
Qed.  
  
(** The max height of a singleton regex set is just the height of the 
    regex contained in the set *)  
Lemma max_height_singleton : forall (r : re),
  max_height_re_set {[r]} = re_height r.
Proof.
  induction r; unfold max_height_re_set; simpl in *. 
  - (* Void *) replace {[ Void ]} with (gset_singleton Void) by set_solver.
    rewrite set_fold_singleton. reflexivity.
  - (* Epsilon *) replace {[ Epsilon ]} with (gset_singleton Epsilon) by set_solver.
    rewrite set_fold_singleton. reflexivity.
  - (* Atom *) replace {[ Atom c ]} with (gset_singleton (Atom c)) by set_solver.
    rewrite set_fold_singleton. reflexivity.
  - (* Union *) replace {[ Union r1 r2 ]} with (gset_singleton (Union r1 r2)) by set_solver.
    rewrite set_fold_singleton. reflexivity.
  - (* Concat *) replace {[ Concat r1 r2 ]} with (gset_singleton (Concat r1 r2)) by set_solver.
    rewrite set_fold_singleton. reflexivity.
  - (* Star *) replace {[ Star r ]} with (gset_singleton (Star r)) by set_solver.
    rewrite set_fold_singleton. reflexivity.
Qed.    

Lemma height_lemma :
  ∀ (X : nat) (rs : gset re),
    max_height_re_set rs <= X <-> 
    ∀ (r : re), r ∈ rs -> re_height r <= X.
Proof.
  unfold max_height_re_set. intros X rs. revert rs.
  (* [n] is the intermediate result of a [set_fold] *)
  apply (set_fold_ind_L
    (fun (n : nat) (rs : gset re) => 
      n ≤ X <-> ∀ r : re, r ∈ rs → re_height r ≤ X)).
  - split; try lia. intros. set_solver. 
  - intros r rs' n H1 H2.
    set_unfold. split; intros.
    + destruct H0 as [Heq | Hin].
      * subst. lia.
      * apply H2 in Hin; lia.
    + assert (re_height r <= X).
      { apply H. auto. }
      assert (n <= X); try lia.
      apply H2. intros. apply H. auto.
Qed. 
      
(** The max height of an Antimirov derivative is at most twice the height
    of the original regex. *)
Lemma a_deriv_height : forall (c : char) (r : re),
  max_height_re_set (a_der r c) <= 2 * re_height r.
Proof.
  induction r; simpl; try unfold "∅".
  - (* Void *) rewrite max_height_empty_set. lia.
  - (* Epsilon *) rewrite max_height_empty_set. lia.
  - (* Atom *) destruct (char_dec c c0).
    + unfold max_height_re_set.
      rewrite max_height_singleton.
      simpl. lia.
    + rewrite max_height_empty_set. lia.
  - (* Union *) rewrite max_height_union. lia.
  - (* Concat *) destruct (isEmpty r1) eqn:E.
    + apply height_lemma.
      intros. simpl in *.
      (* [set_unfold] looks at statements involving ∈ and rewrites them *)
      set_unfold. destruct H as [[x [H11 H12]] | H2].
      * rewrite height_lemma in IHr1.
        apply IHr1 in H12. subst; simpl in *; lia. 
      * rewrite height_lemma in IHr2.
        apply IHr2 in H2. simpl in *. lia.
    + (* isEmpty r1 = false *) 
      apply height_lemma. intros. simpl in *. 
      set_unfold.
      destruct H as [x [H1 H2]].
      subst; simpl. 
      rewrite height_lemma in IHr1.
      specialize (IHr1 _ H2). lia.
  - (* Star *) apply height_lemma. intros; simpl in *.
    set_unfold. destruct H as [x [H1 H2]].
    subst; simpl.
    rewrite height_lemma in IHr.
    specialize (IHr _ H2). lia.
Qed.

(******************************************************************************)




(* Helper lemma: proving that [map] presreves the size of a [gset] 
   - We need to type annotation on the term [(set_map f s)], otherwise 
     Coq can't figure out which typeclass instance for [set_size] to use *)
Lemma map_preserves_set_size : 
  forall (f : re -> re) (s : gset re),
  set_size ((set_map f s) : gset re) = set_size s.
Proof.
  intros f s.
  unfold set_size. simpl. 
  induction s using set_ind_L; eauto.
  rewrite set_map_union_L.
  rewrite set_map_singleton. 
  repeat (rewrite elements_union_singleton).
  - simpl. rewrite IHs. eauto. 
  - assumption.
  - (* Goal: f x ∉ set_map f X *)
    set_unfold.
    intros H'. 
    destruct H' as [x0 [H1 H2]].
Admitted. (* TODO: not sure how to prove the last goal *)
  
(* Union Bound for the size of two sets *)
Lemma set_size_union_bound : forall (rs1 rs2 : gset re),
  set_size (rs1 ∪ rs2) <= set_size rs1 + set_size rs2.
Proof.
  intros.
  induction rs2 using set_ind_L.
  - (* rs2 = ∅ *)
    replace (set_size ∅) with (size (∅ : gset re)) by set_solver. 
    rewrite size_empty.
    rewrite Nat.add_0_r.
    replace (set_size (rs1 ∪ (∅ : gset re))) with (size (rs1 ∪ (∅ : gset re))) 
      by set_solver.
    replace (set_size rs1) with (size rs1) by set_solver.
    rewrite size_union_alt.
    replace ((∅ : gset re) ∖ rs1) with (∅ : gset re) by set_solver.
    rewrite size_empty. 
    lia.
  - (* rs2 = {[ x ]} ∪ X *)
    unfold set_size. simpl.
    rewrite elements_union_singleton; eauto.
    unfold set_size in IHrs2; simpl in *.
    replace (rs1 ∪ ({[x]} ∪ X)) with ({[ x ]} ∪ (rs1 ∪ X)) by set_solver.
    rewrite elements_union_singleton.
    + simpl. lia.
    + set_unfold. unfold not. intros. destruct H0 as [H1 | H2].
      * admit. (* TODO: not sure how to prove that x ∈ rs1 *)
      * apply H in H2. destruct H2.
Admitted.      
      
  

(* Number of Antimirov derivatives is linear in the size of the regex *)
Lemma num_antimirov_derivs_linear_in_re_size : forall (c : char) (r : re),
  exists (k : nat), set_size (a_der r c) <= k * re_size r.
Proof.
  induction r; simpl.
  - (* Void *) eexists. replace (set_size ∅) with 0 by set_solver. lia.
  - (* Epsilon *) eexists. replace (set_size ∅) with 0 by set_solver. lia.
  - (* Atom *) destruct (char_dec c c0).
    + exists 1. 
      unfold set_size; simpl.
      rewrite elements_singleton.
      simpl. lia.
    + eexists. 
      replace (set_size ∅) with 0 by set_solver. lia.
  - (* Union *) destruct IHr1 as [k1 IHr1].
    destruct IHr2 as [k2 IHr2]. eexists.
    rewrite set_size_union_bound.
    + eapply Nat.le_trans. eauto.
      admit. (* TODO: not sure why we can't apply [Nat.plus_le_cases] here *)
  - (* Concat *) destruct IHr1 as [k1 IHr1].
    destruct IHr2 as [k2 IHr2].
    destruct (isEmpty r1) eqn:E.
    + (* isEmpty r1 = true *)    
      admit. (* TODO *)
    + (* isEmpty r2 = false *)
      exists k1.
      rewrite map_preserves_set_size.
      lia.
  - (* Star *)
    destruct IHr as [k H].
    exists k.
    rewrite map_preserves_set_size. 
    lia. 
Admitted.    

