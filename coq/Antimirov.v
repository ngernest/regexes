Require Import Regex ReCountable.
Require Export Lia Nat.

(* If r is a regex and a is a char, then a partial derivative
   is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
   We can construct sets of partial derivatives (Antimirov derivatives). *)

(* Antimirov derivative of a regex [re] with respect to a char [a] *)
(* Note that gsets are finite *)
Fixpoint a_der (r : re) (a : char) : gset re :=
  match r with
  | Void => ∅
  | Epsilon => ∅
  | Atom b => if char_dec a b then {[ Epsilon ]} else ∅
  | Union r1 r2 => (a_der r1 a) ∪ (a_der r2 a)
  | Concat r1 r2 => 
    if isEmpty r1 
      then (set_map (fun r => Concat r r2) (a_der r1 a)) ∪ (a_der r2 a) 
    else (set_map (fun r => Concat r r2) (a_der r1 a))
  | Star r => set_map (fun r' => Concat r' (Star r)) (a_der r a)
  end.


(* Takes the Antimirov derivative wrt a string *)
Fixpoint a_der_str (r : re) (s : string) : gset re :=
  match s with
  | [] => {[ r ]}
  | (c :: cs) => set_bind (fun r => a_der_str r cs) (a_der r c)
  end.

(** Applies Antimirov point-wise to each regex in [rs] 
    - [set_bind] is like [concatMap] for the list monad but using 
      set union instead *)
Definition a_der' (rs : gset re) (c : char) : gset re :=
  set_bind (fun r => a_der r c) rs.

Definition nullable' (rs : gset re) : bool.
  Admitted. (* TODO *)

(** see [antimirov_matches] below *)
Definition a_der_str' (r : re) (s : string) : gset re :=
  fold_left a_der' s {[ r ]}.

(**  A version of [matches'] but for Antimirov *)
Definition antimirov_matches (r : re) (s : string) : bool :=
  nullable' (fold_left a_der' s {[ r ]}).

(* Correctness theorems we could prove for Antimirov:
1. forall r s, matches r s <-> antimirov_matches r s = true
2. forall r s, antimirov_matches r s = true <-> brzozowski_matches r s = true
3. the regex sum of all regexes in the Antimirov set is equivalent (up to ACI)
   to Brzozowski

(extension: compute a finite automaton)
*)


Lemma a_der_str_eps : forall (c : char) (s : string),
  a_der_str Epsilon s ⊆ {[ Epsilon ]}.
Proof. 
  induction s.
  - simpl. set_solver. 
  - simpl. unfold set_bind. rewrite elements_empty. 
    simpl. set_solver.
Qed.

Lemma subset_trans (A B C : gset re) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. set_solver. Qed.

Lemma a_der_str_atom : forall (c : char) (s : string),
  a_der_str (Atom c) s ⊆ {[ Epsilon; Atom c]}.
Proof. 
  induction s.
  - simpl. set_solver. 
  - simpl. destruct (char_dec a c);
    unfold set_bind. 
    + rewrite elements_singleton. simpl. 
      remember a_der_str_eps as H. 
      apply subset_trans with (B := {[ Epsilon ]}).
      * replace (a_der_str Epsilon s ∪ ∅) with (a_der_str Epsilon s) by set_solver.
        apply (H c s). 
      * apply union_subseteq_l. 
    + rewrite elements_empty. simpl. 
      set_solver.
Qed.


(* Definition a := ascii_of_nat 1.
Definition b := ascii_of_nat 2. *)
(* Compute (a_der_str (Union (Atom a) (Atom b)) [a]). *)

(* Generates the (overestimated) set of all possible antimirov derivatives of r, 
   with respect to any word *)
Fixpoint A_der (r : re) : gset re :=
  match r with
  | Void => {[ Void ]}
  | Epsilon => {[ Epsilon ]}
  | Atom b => {[ Epsilon; Atom b ]}
  | Union r1 r2 => (A_der r1) ∪ (A_der r2) ∪ {[ Union r1 r2 ]}
  | Concat r1 r2 => (A_der r2) ∪ (set_map (fun r' => Concat r' r2) (A_der r1))
    ∪ {[ Concat r1 r2 ]}
  | Star r => (set_map (fun r' => Concat r' (Star r)) (A_der r))
    ∪ {[ Star r ]}
  end.

Lemma re_in_A_der : forall (r : re), r ∈ A_der r.
Proof. induction r; simpl; set_solver. Qed.

(* Let r be a regex. We know that A_der r is finite.
   With this lemma, we show that the set of Antimirov derivatives of r 
   with respect to any nonempty word is finite. 
   i.e. {a_der r w | w ∈ Σ+} is finite *)
Theorem a_finite (r : re) : forall (a : re), a ∈ A_der r -> 
  forall (c : char), a_der r c ⊆ A_der r.
Proof. intros. Admitted.

(* Alternate statement *)
Theorem a_finite' (r : re) : forall (s : string), a_der_str r s ⊆ A_der r.
Proof. 
  unfold "⊆", set_subseteq_instance. intros. 
  induction r; destruct s; eauto; try set_solver.
  - remember (a_der_str_atom c (a :: s)) as H1. 
    simpl. eapply elem_of_weaken. apply H. apply H1.
  - simpl in H. destruct (isEmpty r1). admit. admit.
  - simpl. specialize (re_in_A_der (Star r)) as H1.
    admit.
Admitted.

(* B(r) : list re := {fold sum a | a ⊂ A(r)} *)
(* if a string matches the antimirov, it matches wrt matching *)

(* antimirov generates finite sets. can sum them together to get brzozowski *)
(* finitely many b ders: for all r, |{B_w(r) | w word}| is finite *)
(* a brzozowski der is a sum of antimirov derivatves *)
(* wrt these rewrite rules:
a + a = a
A + b = b + a if a < b
A + (b + c) = (a + b) + c
(A + b) + b -> a + b
(A + c) + b -> (a + b) + c
 *)

(* Applies the Antimirov derivative to a whole set of regexes and takes the union *)
Definition aderiv (c : char) (rs : gset re) : gset re :=
  set_bind (fun r => a_der r c) rs.

(** An [Inductive] saying what it means for a string to match a set of regexes 
   - [matches_set_here]: if [s] matches [r], then [s] matches any regex set 
      containing [r] 
   - [matches_set_there]: if [s] matches a regex set [rs], 
       then [s] matches the union of [rs] with any other singleton regex set *)
Inductive matches_set : string -> gset re -> Prop :=
  | matches_set_here (r : re) (s : string) (rs : gset re) : 
      matches r s -> r ∈ rs -> 
      matches_set s rs
  | matches_set_there (r : re) (s : string) (rs : gset re) : 
      matches_set s rs -> 
      matches_set s ({[ r ]} ∪ rs).

(* Adapted from https://monog.ufop.br/server/api/core/bitstreams/d7d18cf6-ff09-4b32-99a6-d87235f7a3ce/content *)
Lemma a_der_weakening : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> 
  matches_set s (rs ∪ rs').
Proof.
  intros. induction H.
  - eapply matches_set_here. apply H. 
    apply elem_of_union_l. apply H0.
  - replace ({[r]} ∪ rs ∪ rs') with ({[r]} ∪ (rs' ∪ rs)) by set_solver.
    eapply matches_set_there.
    replace (rs' ∪ rs) with (rs ∪ rs') by set_solver.
    apply IHmatches_set.
Qed.

(******************************************************************************)
(* Examining the height of Antimirov derivatives 
   Inspired by https://www.weaselhat.com/post-819.html *)

(* Computes the size of a regex (no. of AST nodes) *)
Fixpoint re_size (r : re) : nat :=
  match r with
  | Void => 0
  | Epsilon => 1
  | Atom _ => 1
  | Concat re1 re2 => 1 + re_size re1 + re_size re2
  | Union re1 re2 => 1 + re_size re1 + re_size re2
  | Star re' => 1 + re_size re'
  end.

(* Computes the height of a regex 
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

(* Computes the maximum height of a set of regexes *)
Definition max_height_re_set (rs : gset re) : nat := 
  set_fold (fun r acc => max (re_height r) acc) 0 rs.

Search set_fold.  

(* The max height over a union of two sets is just the max height of each 
   of the constituent subsets *)
Lemma max_height_union (s1 s2 : gset re) :
  max_height_re_set (s1 ∪ s2) = max (max_height_re_set s1) (max_height_re_set s2).
Proof.
  Admitted. (* TODO *)

(* Empty set has [max_height = 0] *)
Lemma max_height_empty_set : 
  max_height_re_set gset_empty = 0. 
Proof.
  unfold max_height_re_set.
  apply set_fold_empty.
Qed.

Lemma gset_elements_singleton {A : Type} `{Countable A} (x : A) :
  gset_elements (gset_singleton x) = [x].
Proof.
  eapply set_eq.
  split; intros.
  set_unfold. 
  destruct H0. 
  destruct H0.
  subst.
  apply elem_of_map_to_list.
  
  
Admitted. (* TODO *)


(** Folding a function [f] over a singleton set is just the same as applying 
    [f] to the element in the set, along with the base case *)
Lemma set_fold_singleton (f : re -> nat -> nat) (b : nat) (r : re) :
  set_fold f b (gset_singleton r) = f r b.
Proof.
  unfold set_fold, elements; simpl.
  rewrite gset_elements_singleton.
  simpl. reflexivity.
Qed.  
  
(* The max height of a singleton regex set is just the height of the 
    regex contained in the set *)  
Lemma max_height_singleton : forall (r : re),
  max_height_re_set {[r]} = re_height r.
Proof.
  induction r; unfold max_height_re_set; simpl in *. 
  - (* Void *)
    replace {[ Void ]} with (gset_singleton Void) by set_solver.
    rewrite set_fold_singleton.
    reflexivity.
  - (* Epsilon *)
    replace {[ Epsilon ]} with (gset_singleton Epsilon) by set_solver.
    rewrite set_fold_singleton.
    reflexivity.
  - (* Atom *)
    replace {[ Atom c ]} with (gset_singleton (Atom c)) by set_solver.
    rewrite set_fold_singleton.
    reflexivity.
  - (* Union *) 
    replace {[ Union r1 r2 ]} with (gset_singleton (Union r1 r2)) by set_solver.
    rewrite set_fold_singleton.
    reflexivity.
  - (* Concat *)
    replace {[ Concat r1 r2 ]} with (gset_singleton (Concat r1 r2)) by set_solver.
    rewrite set_fold_singleton.
    reflexivity.
  - (* Star *)
    replace {[ Star r ]} with (gset_singleton (Star r)) by set_solver.
    rewrite set_fold_singleton.
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
  - split; try lia. 
    intros.
    set_solver. 
  - intros r rs' n H1 H2.
    set_unfold. split; intros.
    + destruct H0 as [Heq | Hin].
      * subst. lia.
      * apply H2 in Hin; lia.
    + assert (re_height r <= X).
      { apply H. auto. }
      assert (n <= X); try lia.
      apply H2.
      intros.
      apply H. auto.
Qed.      
      

 

  
(* The max height of an Antimirov derivative is at most twice the height
   of the original regex. *)
Lemma a_deriv_height : forall (c : char) (r : re),
  max_height_re_set (a_der r c) <= 2 * re_height r.
Proof.
  induction r; simpl; try unfold "∅".
  - (* Void *)
    rewrite max_height_empty_set. lia.
  - (* Epsilon *)
    rewrite max_height_empty_set. lia.
  - (* Atom *)
    destruct (char_dec c c0).
    + (* c = c0 *)
      unfold max_height_re_set.
      rewrite max_height_singleton.
      simpl. lia.
    + (* c <> c0 *)
      rewrite max_height_empty_set.
      lia.
  - (* Union *)
    rewrite max_height_union.
    lia.
  - (* Concat *)
    destruct (isEmpty r1) eqn:E.
    + apply height_lemma.
      intros. simpl in *.
      (* [set_unfold] looks at statements involving ∈ and rewrites them *)
      set_unfold.
      destruct H as [[x [H11 H12]] | H2].
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
      specialize (IHr1 _ H2).
      lia.
  - (* Star *) 
    apply height_lemma. intros; simpl in *.
    set_unfold.
    destruct H as [x [H1 H2]].
    subst; simpl.
    rewrite height_lemma in IHr.
    specialize (IHr _ H2). 
    lia.
Qed.
  

(******************************************************************************)
(* No. of Antimirov derivatives is linear in the size of the regex *)

(* Not sure why this doesn't typecheck *)
(* Lemma map_preserves_set_size : forall (f : re -> re) (s : gset re),
  set_size (set_map f s) = set_size s. *)
  

Lemma num_antimirov_derivs_linear_in_re_size : forall (c : char) (r : re),
  exists (k : nat), set_size (a_der r c) <= k * re_size r.
Proof.
  induction r; simpl.
  - (* Void *)
    eexists. replace (set_size ∅) with 0 by set_solver. lia.
  - (* Epsilon *)
    eexists. replace (set_size ∅) with 0 by set_solver. lia.
  - (* Atom *)
    destruct (char_dec c c0).
    + (* c = c0 *)
      exists 1. 
      unfold set_size; simpl.
      rewrite elements_singleton.
      simpl. lia.
    + (* c <> c0 *)
      eexists. 
      replace (set_size ∅) with 0 by set_solver. lia.
  - (* Union *)
    destruct IHr1 as [k1 IHr1].
    destruct IHr2 as [k2 IHr2].
    eexists.
    assert (set_size (a_der r1 c ∪ a_der r2 c) <= 
      set_size (a_der r1 c) + set_size (a_der r2 c)).
    { admit. (* TODO *) }
    admit.
  - (* Concat *)
    destruct IHr1 as [k1 IHr1].
    destruct IHr2 as [k2 IHr2].
    destruct (isEmpty r1) eqn:E.
    + (* isEmpty r1 = true *)
      admit. (* TODO *)
    + (* isEmpty r2 = false *)
      eexists.
      admit. (* TODO: not sure how to get 
      {[
        assert (set_size (set_map (λ r : re, Concat r r2) (a_der r1 c))
          = set_size (a_der r1 c))
      ]} 
      to typecheck. 
      (But the idea is to prove that calling [map] doesn't change the 
      size of the set -- see [map_preserves_set_size] above. *)
  - (* Star *)
    eexists. 
    admit. (* TODO: Same problem as the [Concat] case *)      
Admitted.    
