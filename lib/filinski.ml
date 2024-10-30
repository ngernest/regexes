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
    (* [k'] is a single-use continuation, used only in the [Star] case *)
    let k' (bf : bool) (ss : char list) : bool = 
      re_match r0 (fun b' s' -> b' && re_match (Star r0) k b' s') bf ss in 
    k b cs || k' false cs 
  

(** Determines whether a string matches a regex *)    
let re_matchtop (r : re) (cs : char list) : bool = 
  re_match r (fun _ xs -> List.is_empty xs) true cs

(* ------------ A defunctionalized termination-augmented matcher ------------ *)

type cont = 
  | CInit 
  | CThen of re * cont 
  | CStar of re * cont 

let fmatch (r : re) (k : cont) (b : bool) (cs : char list) : bool = 
  failwith "TODO: fmatch "


(* TODO: look at fig 3 in the Filinski paper (defunctionalized matcher) *)  

