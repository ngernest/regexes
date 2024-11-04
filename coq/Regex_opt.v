Require Export List Bool Ascii String Arith Lia Nat.
Export ListNotations BoolNotations.

Require Import Regex.

(* Smart constructors for regexes *)

(* Smart constructor for [Union] *)
Definition union_opt (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (_, Void) => r1 
  | (Void, _) => r2 
  | (_, _) => Union r1 r2 
  end.

(* Smart constructor for [Concat] *)
Definition concat_opt (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (Void, _) => Void 
  | (_, Void) => Void 
  | (Epsilon, _) => r2 
  | (_, Epsilon) => r1 
  | (_, _) => Concat r1 r2 
  end.

(* Smart constructor for [Star] *)
Definition star_opt (r : re) := 
  if isEmpty r then Epsilon 
  else match r with 
  | Star r' => Star r' 
  | _ => Star r
  end.


