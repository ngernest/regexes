open! Base

(* -------------------------------------------------------------------------- *)
(*                               1.1 Background                               *)
(* -------------------------------------------------------------------------- *)

(* The stuff in this section is largely the same as [harper.ml], 
   modulo some renaming *)

(** A datatype for regular expressions *)
type re = 
  | Void 
  | Eps 
  | Char of char 
  | Seq of re * re
  | Alt of re * re 
  | Star of re 

(** [omatch] matches some initial segment of [cs] against the regex [r],
    and pases the corresponding final segment to the continuation [k] *)
let rec omatch (r : re) (k : char list -> bool) (cs : char list) : bool = 
  match r, cs with 
  | Void, _ -> false 
  | Eps, _ -> k cs 
  | Char _, [] -> false 
  | Char c, c' :: cs -> if Char.equal c c' then k cs else false 
  | Alt (r1, r2), _ -> 
    omatch r1 k cs || omatch r2 k cs 
  | Seq (r1, r2), _ -> 
    omatch r1 (fun s' -> omatch r2 k s') cs
  | Star r0, _ -> 
    k cs || omatch r0 (fun s' -> omatch r k s') cs

(** Determines whether a string matches a regex *)    
let omatchtop (r : re) (cs : char list) : bool = 
  omatch r List.is_empty cs

(* -------------------------------------------------------------------------- *)
(*                          2.1 Ensuring termination                          *)
(* -------------------------------------------------------------------------- *)

(* --------------------- A termination-augmented matcher -------------------- *)

(** Same as [omatch], but with an extra argument [b], which tracks whether 
    the character has been consumed since the start of the current iteration. 
    Intuition: 
    - [b] is set to true after a successful [Char c] match 
    - [b] is cleared before matching the body [r0] of an iteration [Star r0] 
    - [b] is passed along unchanged for all other cases *)
let rec re_match (r : re) (k : bool -> char list -> bool) 
  (b : bool) (cs : char list) : bool = 
  match r, cs with 
  | Void, _ -> false 
  | Eps, _ -> k b cs 
  | Char _, [] -> false 
  | Char c, c' :: cs -> if Char.equal c c' then k b cs else false 
  | Alt (r1, r2), _ -> 
    re_match r1 k b cs || re_match r2 k b cs 
  | Seq (r1, r2), _ -> 
    re_match r1 (fun s' -> re_match r2 k s') b cs
  | Star r0, _ -> 
    (* [k'] is a single-use continuation, used only in the [Star] case 
       (Filinski says the purpose of [k'] is to satsify some syntactic property 
        later on in the paper) *)
    let k' (bf : bool) (ss : char list) : bool = 
      re_match r0 (fun b' s' -> b' && re_match (Star r0) k b' s') bf ss in 
    k b cs || k' false cs 
  

(** Determines whether a string matches a regex *)    
let re_matchtop (r : re) (cs : char list) : bool = 
  re_match r (fun _ xs -> List.is_empty xs) true cs

(* ------------ A defunctionalized termination-augmented matcher ------------ *)

(** Datatype for defunctionalized continuations: 
    these keep track of the free variables in the body of the continuation *)
type cont = 
  | CInit 
  (* [CThen (r, k)] corresponds to [fun b s -> match r k b s] *)
  | CThen of re * cont 
  (* [CStar (r, k)] represents [CThen (Star r, k)], but also checks whether 
     the guard [b] is true, i.e. [fun b s -> b && match r k b s] *)
  | CStar of re * cont 

let rec fmatch (r : re) (k : cont) (b : bool) (s : char list) : bool = 
  match r, s with 
  | Char _, [] -> false 
  | Char c, c' :: s' -> Char.equal c c' && apply k true s' 
  | Eps, _ -> apply k b s 
  | Seq (r1, r2), _ -> fmatch r1 (CThen (r2, k)) b s
  | Void, _ -> false 
  | Alt (r1, r2), _ -> fmatch r1 k b s || fmatch r2 k b s 
  | Star r0, _ -> 
    apply k b s || apply (CThen (r0, CStar (r0, k))) false s 

(** Builds up the body of the continuation *)    
and apply (k : cont) (b : bool) (s : char list) : bool = 
  match k, s with 
  | CInit, _ -> false 
  | CThen (r, k), _ -> fmatch r k b s 
  | CStar (r, k), _ -> b && fmatch (Star r) k b s

(** Top-level regex matcher *)
let fmatchtop (r : re) (s : char list) : bool = fmatch r CInit true s 


