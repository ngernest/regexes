Require Import Regex ReCountable.
Generalizable All Variables.

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

(* Fixpoint a_der_str (r : re) (s : string) : gset re :=
  match s with
  | [] => ∅
  | (c :: cs) => set_map (fun r => a_der r) *)

(* gsets are finite *)

(* A(r) = all possible antimirov ders of r (list), wrt any word *)
(* A(c) = {0, e, c} A(0) = {0} A(e) = {0, e} 
   A(a + b) = A(a) ∪ A(b) + {a + b} *)
(* A(ab) = A(b) ∪ {a'b | a' ∈ A(a)} ∪ {ab} *)
(* A(a^#) = {a'a^* | a' ∈ A(a)} ∪ {a*} *)
(* A' is same except can't take der wrt e *)
(* then a_der r a subset A(r) *)
(* wts that antimirov ⊂ A *)
(* forall s, a_der s r ⊂ A(r) *)
(* therefore, finitely many possible antimirov ders *)

(* a ∈ A(r) -> ∀ c, A_c(a) ⊆ A(r) *)

(* B(r) : list re := {fold sum a | a ⊂ A(r)} *)
(* if a string matches the antimirov, it matches wrt matching *)
(*  *)

(* antimirov generates finite sets. can sum them together to get brzozowski *)
(* finitely many b ders: for all r, |{B_w(r) | w word}| is finite *)
(* a brzozowski der is a sum of antimirov derivatves *)

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
