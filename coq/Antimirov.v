Require Import Regex ReCountable.

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
  - simpl in *. destruct (isEmpty r1).
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
