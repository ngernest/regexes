Require Import List Bool Ascii String.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope char_scope.

(* Some notation so that we can use single quotes to represent chars
   https://stackoverflow.com/questions/26112349/single-quote-notation-for-characters-in-coq *)

Notation "''c''" := "c" : char_scope.
Notation "''a''" := "a" : char_scope.

(* Note that the literal ['a'] has type [ascii], aka [char] *)
Check 'a'.

(* Polymorphic regular expressions: regexes in [re T] describe 
   strings with characters drawn from [T], i.e. lists of elements of [T]. 
   (Adapted from HW3) *)
Inductive re (T : Type) : Type :=
  | Void
  | Eps
  | Char (c : T)
  | Seq (r1 r2 : re T)
  | Alt (r1 r2 : re T)
  | Star (r : re T). 


