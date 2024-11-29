Require Export List ListSet Ascii Bool.
Import ListNotations.
Require Import Regex Edelmann Antimirov RegexOpt.

(* Work in progress: proving that the underlying sets 
   for zippers & Antimirov derivatives are equivalent *)

Definition context_to_re (ctx : context) : re :=
  List.fold_left concat ctx Epsilon.

(* Definition underlying_zipper_set (r : re) (c : char) :=
  zipper_map  *)
  