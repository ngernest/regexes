Require Import Regex ReCountable.

(* If r is a regex and a is a char, then a partial derivative
   is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
   We can construct sets of partial derivatives (Antimirov derivatives). *)

Fixpoint a_der (r : re) (a : char) `{Countable re} : gset re :=
  match r with
  | Empty => gset_empty
  | Epsilon => gset_empty
  | Atom b => if char_dec a b then gset_singleton Epsilon else gset_empty
  | Union r1 r2 => gset_union (a_der r1 a) (a_der r2 a)
  | Concat r1 r2 => 
    if eps r1 
      then gset_union (set_map (fun r => Concat r r2) (a_der r1 a)) (a_der r2 a) 
    else (set_map (fun r => Concat r r2) (a_der r1 a))
  | Star r => set_map (fun r' => Concat r' (Star r)) (a_der r a)
  end.
  