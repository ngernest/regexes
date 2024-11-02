Require Import List Bool Ascii String Arith Lia Nat.
Import ListNotations.
Import BoolNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope char_scope.

(* This allows us to write [Program Fixpoint] *)
Require Import Coq.Program.Wf.

(* Some notation so that we can use single quotes to represent chars *)
Notation "''a''" := "a" : char_scope.
Notation "''b''" := "b" : char_scope.

(* Note that the literal ['a'] has type [ascii], aka [char] *)
Check 'a'.

(* Polymorphic regular expressions: regexes in [re T] describe 
   strings with characters drawn from [T], i.e. lists of elements of [T]. 
   (Adapted from HW3) *)
Inductive re : Type :=
  | Void
  | Eps
  | Char (c : ascii)
  | Seq (r1 r2 : re)
  | Alt (r1 r2 : re)
  | Star (r : re). 

(* [re_size] computes the size of a regular expression. 
   (This acts as a well-founded recursion measure we use to convince Coq that 
   the function [re_match] below terminates) *)
Fixpoint re_size (r : re) : nat :=
  match r with
  | Void => 1
  | Eps => 1
  | Char _ => 1
  | Alt r1 r2 => 1 + re_size r1 + re_size r2
  | Seq r1 r2 => 1 + re_size r1 + re_size r2
  | Star r0 => 1 + re_size r0
  end.

(* Helper function for character equality *)
Definition ascii_eqb (c1 c2 : ascii) : bool := 
  if ascii_dec c1 c2 then true else false.  

(* [re_match] is a regex matcher written in continuation passing style:
  - [k] is a continuation, says what to do with remainder of string 
  after matching current character 
  - [b] is a bool that tracks whether the character has been consumed
  since the start of the current iteration. Intuition: 
  ++ [b] is set to true after a successful [Char c] match 
  ++ [b] is cleared before matching the body [r0] of an iteration [Star r0] 
  ++ [b] is passed along unchanged for all other cases *)
Program Fixpoint re_match (r : re) (k : bool -> list ascii -> bool) 
  (b : bool) (cs : list ascii) 
  {measure (re_size r)} : bool := 
  match (r, cs) with
  | (Void, _) => false
  | (Eps, _) => k b cs
  | (Char _, []) => false
  | (Char c, c' :: s') => ascii_eqb c c' && k b s' 
  | (Alt r1 r2, _) => (re_match r1 k b cs) || (re_match r2 k b cs)
  | (Seq r1 r2, _) => re_match r1 (fun b' cs' => re_match r2 k b' cs') b cs
  | (Star r0, _) =>
    (* [k'] is a single-use continuation, used only in the [Star] case 
      (Filinski says the purpose of [k'] is to satsify some syntactic 
      property later in the paper) *)
    let k' := fun bf ss =>
      re_match r0 (fun b' s' => b' && re_match (Star r0) k b' s') bf ss 
    in
     (k b cs) || (k' false cs)
   end.
(* Solve Obligations with (simpl in *; try lia). *)

Next Obligation. 
  simpl in *. lia.
Defined.  

Next Obligation.
  simpl in *. lia.
Defined.  

Next Obligation.
  simpl in *. lia.
Defined.  

Next Obligation.
  simpl in *. lia.
Defined.  

Next Obligation.
  simpl in *. 
  specialize re_match with (r := Star r0).
  apply re_match in k.
  Search (S _ < S _ -> _ < _).


