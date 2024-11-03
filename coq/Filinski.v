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
  ++ [b] is passed along unchanged for all other cases 

  Note: we modified this function to take in an extra [fuel] argument 
  as we weren't able to convince Coq that [re_size r] is decreasing for the 
  [Star] case *)
Fixpoint re_match (fuel : nat) (r : re) (k : bool -> list ascii -> bool) 
  (b : bool) (cs : list ascii) : bool := 
  match fuel with
  | 0 => false
  | S n => 
    match (r, cs) with
    | (Void, _) => false
    | (Eps, _) => k b cs
    | (Char _, []) => false
    | (Char c, c' :: s') => ascii_eqb c c' && k b s' 
    | (Alt r1 r2, _) => (re_match n r1 k b cs) || (re_match n r2 k b cs)
    | (Seq r1 r2, _) => re_match n r1 (fun b' cs' => re_match n r2 k b' cs') b cs
    | (Star r0, _) =>
      (* [k'] is a single-use continuation, used only in the [Star] case 
        (Filinski says the purpose of [k'] is to satsify some syntactic 
        property later in the paper) *)
      let k' := fun bf ss =>
        re_match n r0 (fun b' s' => b' && re_match n (Star r0) k b' s') bf ss 
      in 
      (k b cs) || (k' false cs)
    end
  end.

(** Top-level regex matcher *)
Definition matchtop (r : re) (cs : list ascii) :=
  re_match (S (List.length cs)) r (fun _ s' => 
    match s' with 
    | [] => true 
    | _ => false 
    end) true cs.


(*******************************************************************************)
(* Fig 3: Termination-augmented matcher (first-order version) *)

(* Datatype for defunctionalized continuations: 
  these keep track of the free variables in the body of the continuation.
  - [CThen (r, k)] corresponds to [fun b s -> match r k b s]
  - [CStar (r, k)] represents [CThen (Star r, k)], but also checks whether 
    the guard [b] is true, i.e. [fun b s -> b && match r k b s] *)  
Inductive cont := 
  | CInit
  | CThen (r : re) (k : cont)
  | CStar (r : re) (k : cont).

(* We assign a weight to a pair [(k, b)] *)
Fixpoint weight (k : cont) (b : bool) : nat :=  
  match (k, b) with 
  | (CInit, _) => 0 
  | (CThen r k, _) => re_size r + weight k b 
  | (CStar r k, true) => 1 + re_size r + weight k true 
  | (CStar r k, false) => 0
  end. 
  
(* Note: we added a [fuel] argument to convince Coq that it terminates *)
Fixpoint fmatch 
  (fuel : nat) (r : re) (k : cont) (b : bool) (s : list ascii) : bool :=
  match fuel with 
  | 0 => false 
  | S n =>   
    match (r, s) with
    | (Char _, []) => false
    | (Char c, c' :: s') => ascii_eqb c c' && applyf n k true s'
    | (Eps, _) => applyf n k b s
    | (Seq r1 r2, _) => fmatch n r1 (CThen r2 k) b s
    | (Void, _) => false
    | (Alt r1 r2, _) => fmatch n r1 k b s || fmatch n r2 k b s
    | (Star r0, _) => applyf n k b s || applyf n (CThen r0 (CStar r0 k)) false s
    end
  end

(* [applyf] builds up the body of the continuation *)
with applyf (fuel : nat) (k : cont) (b : bool) (s : list ascii) : bool :=
  match fuel with
  | 0 => false
  | S n => 
    match (k, s) with
    | (CInit, _) => false
    | (CThen r k, _) => fmatch n r k b s
    | (CStar r k, _) => b && fmatch n (Star r) k b s  
    end
  end.

Definition fmatchtop (r : re) (s : list ascii) : bool := 
  fmatch (List.length s) r CInit true s.

