Require Import List Bool.
Import ListNotations.

(* Polymorphic regular expressions: regexes in [re T] describe 
   strings with characters drawn from [T], i.e. lists of elements of [T] *)
Inductive re (T : Type) : Type :=
  | Void
  | Eps
  | Char (c : T)
  | Seq (r1 r2 : re T)
  | Alt (r1 r2 : re T)
  | Star (r : re T). 

