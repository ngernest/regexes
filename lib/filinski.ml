open! Base

(* ----------------------------- 1.1: Background ---------------------------- *)

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
let rec omatch (r : re) (k : char list -> bool) (cs : char list): bool = 
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


