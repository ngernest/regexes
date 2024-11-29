Require Import Antimirov.
Require Import Brzozowski.
Require Import Finite.

(** Examining the height of Antimirov derivatives 
    Inspired by https://www.weaselhat.com/post-819.html *)

(** Computes the size of a regex (no. of AST nodes) *)
Fixpoint re_size (r : re) : nat :=
  match r with
  | Void => 1
  | Epsilon => 1
  | Atom _ => 2
  | Concat re1 re2 => 1 + re_size re1 + re_size re2
  | Union re1 re2 => 1 + re_size re1 + re_size re2
  | Star re' => 1 + re_size re'
  end.

(** Computes the height of a regex 
    (height of the binary tree formed by the AST) *)
Fixpoint re_height (r : re) : nat :=
  match r with
  | Void => 1
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
  elements (({[ x ]}) : gset A) = [x].
Proof.
  simpl. 
  set_unfold.
  rewrite elements_singleton. reflexivity.
Qed.

(** Folding a function [f] over a singleton set is just the same as applying 
    [f] to the element in the set, along with the base case *)
Lemma set_fold_singleton (f : re -> nat -> nat) (b : nat) (r : re) :
  set_fold f b ({[ r ]} : gset re) = f r b.
Proof.
  simpl. unfold set_fold; simpl.
  rewrite elements_singleton.
  simpl. reflexivity.
Qed.  

(** Mapping a function [f] over a singleton set returns a singleton 
    set containing the result [f x].  *)
Lemma set_map_singleton (f : re -> re) (x : re):
  set_map f ({[ x ]} : gset re) = ({[ f x ]} : gset re).
Proof.
  unfold set_map.
  rewrite elements_singleton.
  simpl.
  set_solver.
Qed.  
  
(** The max height of a singleton regex set is just the height of the 
    regex contained in the set *)  
Lemma max_height_singleton : forall (r : re),
  max_height_re_set {[r]} = re_height r.
Proof.
  induction r; 
    unfold max_height_re_set; 
    simpl in *;
    rewrite set_fold_singleton; 
    reflexivity.
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

(* Nonexistent elements have an empty intersection with the original set *)
Lemma empty_intersection_with_absent_element : 
  forall (x : re) (X : gset re), x ∉ X -> X ∩ {[ x ]} = ∅.
Proof. intros. set_solver. Qed.  

(* Subtracting a nonexistent element from a set 
   preserves the original set's size *)
Lemma removing_nonexistent_elem_preserves_size : 
  forall (x : re) (X : gset re), x ∉ X -> size (X ∖ {[ x ]}) = size X.
Proof.
  intros.
  rewrite size_difference_alt.
  rewrite empty_intersection_with_absent_element. 
  rewrite size_empty.
  lia. assumption.
Qed.  

(* Calling [map] on a set results in a set whose size is at most 
   the size of the original set. 
   - Note: We need type annotations on the term [(set_map f s)], otherwise 
     Coq can't figure out which typeclass instance to use for [size] *)
Lemma size_map_upper_bound : 
  forall (f : re -> re) (s : gset re),
  size ((set_map f s) : gset re) <= size s.
Proof.
  intros f s.
  simpl.
  induction s using set_ind_L; eauto.
  rewrite set_map_union_L.
  rewrite set_map_singleton. 
  repeat (rewrite size_union_alt).
  rewrite size_singleton.
  replace (size ({[x]} ∪ X)) with (size ({[ x ]} : gset re) + size (X ∖ {[ x ]})).
  - rewrite size_singleton. 
    assert (size (X ∖ {[ x ]}) = size X).
    { rewrite removing_nonexistent_elem_preserves_size. 
      auto. assumption. }
    rewrite H0. 
    rewrite size_difference_alt.
    assert (
      size (set_map f X : gset re) - size (set_map f X ∩ {[ f x ]} : gset re) 
      <= size X
    ) by lia.
    X.
  - rewrite <- size_union_alt. auto.
Qed. 
  
(* Union Bound for the size of two sets *)
Lemma set_size_union_bound : forall (rs1 rs2 : gset re),
  size (rs1 ∪ rs2) <= size rs1 + size rs2.
Proof.
  intros.
  rewrite size_union_alt.
  rewrite size_difference_alt. lia.
Qed.

(* The size of the set [A_der r] (which overapproximates the set of 
   Antimirov derivatives) is linear in the size of the original regex *)
Theorem A_der_linear : exists (k : nat), 
  forall (r : re), size (A_der r) <= k * re_size r. 
Proof.
  eexists. intros.
  induction r. 
  - (* Void *)
    unfold A_der, re_size. 
    rewrite size_singleton.
    assert (1 <= 1 * 1) by lia. 
    apply H.
  - (* Epsilon *)
    unfold A_der, re_size. 
    rewrite size_singleton. 
    assert (1 <= 1 * 1) by lia. 
    apply H.
  - (* Atom *)
    unfold A_der, re_size. 
    assert (size ({[ Epsilon; Atom c ]} : gset re) = 2).
    { admit. 
      (* TODO: not sure how to assert that the size has size 2 *) }
    lia. 
  - (* Union *)
    simpl. 
    rewrite set_size_union_bound.
    rewrite size_union_alt.
    rewrite size_difference_alt.
    rewrite size_singleton. 
    X.
  - (* Concat *)
    simpl.
    repeat (rewrite size_union_alt).
    assert (size ((set_map (λ r' : re, (Concat r' r2 : re)) (A_der r1 : gset re)) : gset re)
      <= size (A_der r1 : gset re)).
    { rewrite size_map_upper_bound. lia. } 
    simpl in *. 
    repeat (rewrite size_difference_alt). 
    X.
    admit. (* TODO: not sure how to proceed *)
  - (* Star *)
    simpl.
    rewrite size_union_alt. 
    assert (size ((set_map (λ r' : re, (Concat r' (Star r) : re)) (A_der r : gset re)) : gset re)
      <= size (A_der r : gset re)).
    { rewrite size_map_upper_bound. lia. }
    simpl in *.
    rewrite size_difference_alt.
    rewrite size_singleton.
    X.
Admitted. 
  
(* There exists some constant [k] which upper bounds the size of all Antimirov derivatives w.r.t. a string *) 
Lemma num_antimirov_derivs_linear_in_re_size : exists (k : nat), 
  forall (s : string) (r : re),
    set_size (a_der_str r s) <= k * re_size r.
Proof.
  intros. 
  destruct A_der_linear as [k H].
  exists k. intros.
Admitted. (* TODO *)  
  (* TOOD: need to use some result that all elements of [a_der_str r s] ∈ [A_Der]
     - need to think about whether [A_der] is actually linear in the size of [r]
   *)

  

