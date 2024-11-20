Require Import Regex.
Require Export Lia Nat.

(** If r is a regex and a is a char, then a partial derivative
    is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
    We can construct sets of partial derivatives (Antimirov derivatives) *)

(** Antimirov derivative of a regex [re] with respect to a char [a] *)
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

(** Takes the Antimirov derivative wrt a string *)
Fixpoint a_der_str (r : re) (s : string) : gset re :=
  match s with
  | [] => {[ r ]}
  | (c :: cs) => set_bind (fun r => a_der_str r cs) (a_der r c)
  end.

(** Applies Antimirov point-wise to each regex in [rs] 
    - [set_bind] is like [concatMap] for the list monad but using 
      set union instead *)
Definition a_der_set (rs : gset re) (c : char) : gset re :=
  set_bind (fun r => a_der r c) rs.

(** True if there is a regex in the set which matches the empty string *)
Definition nullable (rs : gset re) : bool :=
  let is_elem_of_bool (x : bool) (s : gset bool) := bool_decide (x ∈ s) in
  is_elem_of_bool true (set_map (fun r => isEmpty r) rs) .

(** A version of [b_matches] but for Antimirov *)
Definition a_matches (r : re) (s : string) : bool :=
  nullable (fold_left a_der_set s {[ r ]}).

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
