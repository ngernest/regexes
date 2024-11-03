Require Import Regex.

(* If r is a regex and a is a char, then a partial derivative
   is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
   We can construct sets of partial derivatives (Antimirov derivatives). *)
Print gset_empty.
Print EqDecision.
Print RelDecision.
Print Countable.

Parameter re_decidable : EqDecision re.
Parameter re_countable : @Countable re re_decidable.

(* Antimirov derivative of a regex [re] with respect to a char [a] *)
Fixpoint a_der (r : re) (a : char) : gset re :=
  match r with
  | Empty => @gset_empty re re_decidable re_countable
  | Epsilon => gset_empty
  | Atom b => if eq_dec a b then gset_singleton Epsilon else gset_empty
  | Union r1 r2 => gset_union (a_der r1 a) (a_der r2 a)
  | Concat r1 r2 => 
    if eps r1 
      then gset_union (set_map (fun r => Concat r r2) (a_der r1 a)) (a_der r2 a) 
    else (set_map (fun r => Concat r r2) (a_der r1 a))
  | Star r => set_map (fun r' => Concat r' (Star r)) (a_der r a)
  end.
  
Definition empty_re_set := @gset_empty re re_decidable re_countable.

(* TODO: not sure how to define the following function which applies the 
   Antimirov derivative to a whole set of regexes and takes the union 
   (see [antimirov.ml])

Definition aderiv (c : char) (rs : gset re) : gset re :=
  set_fold (fun r acc => gset_union (a_der r c) acc) rs empty_re_set. *)


(** An [Inductive] saying what it means for a string to match a set of regexes 
   - [matches_set_here]: if [s] matches [r], then [s] matches any regex set 
      containing [r] 
   - [matches_set_there]: if [s] matches a regex set [rs], 
       then [s] matches the union of [rs] with any other singleton regex set *)
Inductive matches_set : string -> gset re -> Prop :=
  | matches_set_here (r : re) (s : string) (rs : gset re) : 
      matches r s -> 
      @gset_elem_of re re_decidable re_countable r rs -> 
      matches_set s rs
  | matches_set_there (r : re) (s : string) (rs : gset re) : 
      matches_set s rs -> 
      matches_set s (gset_union (gset_singleton r) rs).


(* Adapted from https://monog.ufop.br/server/api/core/bitstreams/d7d18cf6-ff09-4b32-99a6-d87235f7a3ce/content *)
Lemma a_der_weakening : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> 
  matches_set s (gset_union rs rs').
Proof.
  Admitted.
 

    
    