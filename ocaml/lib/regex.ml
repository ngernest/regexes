open Base_quickcheck
open Sexplib.Conv

(** A datatype for regular expressions *)
type re = 
  | Char of char [@quickcheck.generator GeneratoRegexSet.char_lowercase]
  | Void 
  | Epsilon 
  | Seq of re * re 
  | Alt of re * re 
  | Star of re
[@@deriving quickcheck, sexp_of]  

 (** Smart constructor for alternation *)
 let alt (r1 : re) (r2 : re) : re =
  match (r1, r2) with
  | _, Void -> r1
  | Void, _ -> r2
  | _, _ -> Alt (r1, r2)

(** Smart constructor for sequencing *)
let seq (r1 : re) (r2 : re) : re =
  match (r1, r2) with
  | Void, _ -> Void
  | _, Void -> Void
  | _, Epsilon -> r1
  | Epsilon, _ -> r2
  | _, _ -> Seq (r1, r2)

(** Smart constructor for [star]. Note that:
    - Iterating the empty string gives the empty string, 
    - Zero or more occurrences of [Void] is empty
    - Two iterations is the same as one, i.e. [star (Star r) = Star r] *)
let star (re : re) : re =
  match re with
  | Void | Epsilon -> Epsilon
  | Star re' -> Star re'
  | _ -> Star re

(** Computes the {i size} (i.e. length) of a regex *)
let rec re_size (r : re) : int =
  match r with
  | Void -> 0
  | Epsilon -> 1
  | Char _ -> 1
  | Seq (re1, re2) -> 1 + re_size re1 + re_size re2
  | Alt (re1, re2) -> 1 + re_size re1 + re_size re2
  | Star re' -> 1 + re_size re'

(* Computes the height of a regex 
   (i.e. the height of the binary tree formed by the AST) *)
let rec re_height (r : re) : int = 
  match r with 
  | Void -> 0
  | Epsilon -> 1
  | Char _ -> 1
  | Seq (re1, re2) -> 1 + max (re_height re1) (re_height re2)
  | Alt (re1, re2) -> 1 + max (re_height re1) (re_height re2)
  | Star re' -> 1 + re_height re'

(** Checks if a regex accepts the empty string *)
let rec accepts_empty (r : re) : bool = 
  match r with 
  | Char _ | Void -> false
  | Epsilon | Star _ -> true
  | Alt (r1, r2) -> accepts_empty r1 || accepts_empty r2
  | Seq (r1, r2) -> accepts_empty r1 && accepts_empty r2

(** [R] is the type of finite sets of regexes *)  
module RegexSet = struct
  include Set.Make(struct 
    type t = re 
    let compare = compare 
  end)
end

(** [rmap] maps a function over a set of regexes, building a new regex *)
let rmap (f : re -> re) (rs : RegexSet.t) : RegexSet.t = 
  RegexSet.fold (fun r -> RegexSet.add (f r)) rs RegexSet.empty

(** Computes the max height of a regex in a set of regexes [rs] *)
let max_height_re_set (rs : RegexSet.t) : int = 
  RegexSet.fold (fun r acc -> max (re_height r) acc) rs 0
