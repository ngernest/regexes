Require Import Regex.
Require Export Lia.

(** If r is a regex and a is a char, then a partial derivative
    is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
    We can construct sets of partial derivatives (Antimirov derivatives) *)

(* Note that gsets are finite *)
Fixpoint a_der (r : re) (c : char) : gset re :=
  match r with
  | Void => ∅
  | Epsilon => ∅
  | Atom b => if char_dec c b then {[ Epsilon ]} else ∅
  | Union r1 r2 => (a_der r1 c) ∪ (a_der r2 c)
  | Concat r1 r2 => 
    if isEmpty r1 
      then (set_map (fun r => Concat r r2) (a_der r1 c)) ∪ (a_der r2 c) 
    else (set_map (fun r => Concat r r2) (a_der r1 c))
  | Star r => set_map (fun r' => Concat r' (Star r)) (a_der r c)
  end.

(** Takes the Antimirov derivative wrt a string *)
Fixpoint a_der_str (r : re) (s : string) : gset re :=
  match s with
  | [] => {[ r ]}
  | (c :: cs) => set_bind (fun r' => a_der_str r' cs) (a_der r c)
  end.

(** Applies Antimirov point-wise to each regex in [rs] 
    - [set_bind] is like [concatMap] for the list monad but using 
      set union instead *)
Definition a_der_set (rs : gset re) (c : char) : gset re :=
  set_bind (fun r => a_der r c) rs.

Lemma a_der_set_singleton (r : re) (c : char) : 
  a_der_set {[ r ]} c = a_der r c.
Proof. unfold a_der_set. rewrite set_bind_singleton_L. reflexivity. Qed. 
Hint Rewrite a_der_set_singleton : core. 

(** True if there is a regex in the set which matches the empty string *)
Definition nullable (rs : gset re) : bool :=
  let elem_of_bool (x : bool) (s : gset bool) := bool_decide (x ∈ s) in
  elem_of_bool true (set_map (fun r => isEmpty r) rs).

(** True if r matches s, using a_der_set *)
Definition a_matches (r : re) (s : string) : bool :=
  nullable (fold_left a_der_set s {[ r ]}).

(** Alternate definition using a_der_str *)
Definition a_matches' (r : re) (s : string) : bool :=
  nullable (a_der_str r s).

Lemma a_der_set_empty (c : char) : a_der_set ∅ c = ∅.
Proof. unfold a_der_set. set_solver. Qed.
Hint Rewrite a_der_set_singleton : core. 

Lemma fold_left_empty (s : string) : fold_left a_der_set s ∅ = ∅.
Proof. induction s; autorewrite with core; eauto. Qed.
Hint Rewrite fold_left_empty : core.

Lemma set_bind_empty (f : re -> gset re) : set_bind f (∅ : gset re) = ∅.
Proof. set_solver. Qed.
Hint Rewrite set_bind_empty : core.

Lemma set_bind_singleton (f : re -> gset re) (r : re) : 
  set_bind f ({[r ]} : gset re) = f r.
Proof. set_solver. Qed.
Hint Rewrite set_bind_singleton : core.

Lemma set_bind_union (f : re -> gset re) (r1 r2 : gset re) :
  set_bind f (r1 ∪ r2) = set_bind f r1 ∪ set_bind f r2.
Proof. set_solver. Qed. 
Hint Rewrite set_bind_union : core. 

Lemma char_refl : forall (c : char), 
  (if char_dec c c then true else false) = true.
Proof. intros. destruct char_dec; eauto. Qed.
Hint Rewrite char_refl : core. 

Lemma a_matches_matches' (r : re) (s : string) : 
  a_matches r s <-> a_matches' r s.
Proof. 
  induction r; unfold a_matches, a_matches', nullable in *. 
  - X; destruct H1; destruct s; simpl in *;
    autorewrite with core in *; eauto. 
  - X; destruct H1; destruct s; simpl in *;
    autorewrite with core in *; eauto. 
  - X; destruct H1; exists x; split; destruct s; eauto; simpl in *;
    destruct (char_dec a c); subst; autorewrite with core in *; simpl in *. 
    + simpl in *. destruct (char_dec c c). 
      * induction s; eauto; simpl in *; 
        autorewrite with core in *; inversion H0.
      * autorewrite with core in *; inversion H0.
    + destruct (char_dec a c). 
      * contradiction. 
      * autorewrite with core in *. apply H0. 
    + destruct (char_dec c c). 
      * induction s; eauto; autorewrite with core in *; inversion H0. 
      * contradiction. 
    + inversion H0. 
  - X; destruct H9; exists x; split; eauto; destruct s; eauto; simpl; 
    autorewrite with core in *.  
Admitted.

(** Says what it means for a string to match a set of regexes.
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

(** Adapted from https://monog.ufop.br/server/api/core/bitstreams/d7d18cf6-ff09-4b32-99a6-d87235f7a3ce/content *)
Lemma a_der_weakening : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> matches_set s (rs ∪ rs').
Proof.
  intros. induction H.
  - eapply matches_set_here. apply H. 
    apply elem_of_union_l. apply H0.
  - replace ({[r]} ∪ rs ∪ rs') with ({[r]} ∪ (rs' ∪ rs)) by set_solver.
    eapply matches_set_there.
    replace (rs' ∪ rs) with (rs ∪ rs') by set_solver.
    apply IHmatches_set.
Qed.
