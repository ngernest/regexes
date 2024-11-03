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