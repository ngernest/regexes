Require Import Regex.
Require Import Antimirov. 
Require Import Brzozowski.

(** Proving that taking the Antimirov derivative wrt a word will always
    generate a finite set *)

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

(* Crashes Coq *)
(* Definition a := ascii_of_nat 1.
Definition b := ascii_of_nat 2.
Compute (a_der_str (Union (Atom a) (Atom b)) [a]). *)

(** Generates the (overestimated) set of all possible Antimirov derivatives of r, 
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

(** Let r be a regex. We know that A_der r is finite.
    With this lemma, we show that the set of Antimirov derivatives of r 
    with respect to any nonempty word is finite. 
    i.e. {a_der r w | w ∈ Σ+} is finite *)
Theorem a_finite (r : re) : forall (a : re), a ∈ A_der r -> 
  forall (c : char), a_der r c ⊆ A_der r.
Proof. intros. Admitted.

(** Alternate statement *)
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
