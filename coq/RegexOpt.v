Require Export List Bool Ascii String Arith Lia Nat.
Export ListNotations BoolNotations.
Require Import Regex.

(** Smart constructors for regexes *)

(** Smart constructor for [Union] 
    - TODO: finish translating the OCaml [alt] smart constructor to Gallina
      (need to figure out how to satisfy the termination checker)
*)
Fixpoint union (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (_, Void) => r1 
  | (Void, _) => r2 
  | (Union r11 r12, _) => union r11 (union r12 r2)
  | (_, _) => Union r1 r2 
  end.

(** Smart constructor for [Concat] *)
Definition concat (r1 : re) (r2 : re) : re :=
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
Definition star (r : re) := 
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
  | Union r1 r2 => union (N r1) (N r2)
  | Concat r1 r2 => 
    union 
      (union (concat (E r1) (N r2)) (concat (N r1) (E r2)))
      (concat (N r1) (N r2))
  | Star r' => concat (N r') (star (N r'))
  end.
