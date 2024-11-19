Require Export List Bool Ascii String Arith Lia Nat.
Export ListNotations BoolNotations.
Require Import Regex.

(** Smart constructors for regexes *)

(** Smart constructor for [Union] *)
Definition union_opt (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (_, Void) => r1 
  | (Void, _) => r2 
  | (_, _) => Union r1 r2 
  end.

(** Smart constructor for [Concat] *)
Definition concat_opt (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (Void, _) => Void 
  | (_, Void) => Void 
  | (Epsilon, _) => r2 
  | (_, Epsilon) => r1 
  | (_, _) => Concat r1 r2 
  end.

(** Smart constructor for [Star]. Note:
    - Iterating the empty string gives us the empty string
    - Zero or more occurrences of Void is empty
    - Two iterations of [Star] is the same as one *)
Definition star_opt (r : re) := 
  if isEmpty r || isVoid r then Epsilon 
  else match r with 
  | Star r' => Star r' 
  | _ => Star r
  end.

(** Returns [Epsilon] if [r] matches the empty string, 
    otherwise matches [Void] *)
Definition E (r : re) : re :=
  if isEmpty r then Epsilon else Void.

(** Helper function for standardizing regexes: computes L(r) ∖ {∊}
    - TODO: figure out why this works *)
Fixpoint N (r : re) : re :=
  match r with 
  | Void => Void 
  | Epsilon => Epsilon 
  | Atom c => Atom c 
  | Union r1 r2 => union_opt (N r1) (N r2)
  | Concat r1 r2 => 
    union_opt 
      (union_opt (concat_opt (E r1) (N r2)) (concat_opt (N r1) (E r2)))
      (concat_opt (N r1) (N r2))
  | Star r' => concat_opt (N r') (star_opt (N r'))
  end.
