open Base_quickcheck
open Sexplib.Conv

let equal_char = Base.equal_char
let compare_char = Base.compare_char

(** A datatype for regular expressions. 
    - The constructors are ordered in increasing order, i.e. [Void] is the 
      smallest possible [re], followed by [Epsilon], etc. 
    - The derived [compare_re] function is a total order representing <= 
      over regexes
    - For simplicity, we do not generate [Void]s in our QuickCheck generator,
      and we limit the alphabet used by the QC generator to [{a, b}]. *)
type re = 
  | Void [@quickcheck.do_not_generate]
  | Epsilon 
  | Char of (char [@quickcheck.generator Generator.of_list ['a'; 'b']])
  | Seq of re * re 
  | Alt of re * re 
  | Star of re
[@@deriving quickcheck, sexp, equal, compare]  

 (** Smart constructor for alternation: 
    - Void is the identify element for [Alt]
    - Reassociates all the [Alt]s to the left
    - Sorts operands in increasing lexicographic order (using "bubble-sort")
 *)
let rec alt (r1 : re) (r2 : re) : re =
  match (r1, r2) with
  | _, Void -> r1
  | Void, _ -> r2
  | Alt (r11, r12), _ -> alt r11 (alt r12 r2)
  | a, Alt (b, c) -> 
    if compare_re a b > 0 
      then alt b (alt a c)
    else 
      Alt (r1, r2)
  | r1', r2' when compare_re r1' r2' > 0 -> alt r2' r1'
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

(** Optimizes a regex *)  
let rec optimize_re (r : re) : re = 
  match r with 
  | Seq (r', Void) | Seq (Void, r') -> 
      Void
  | Seq (r', Epsilon) | Seq (Epsilon, r') 
  | Alt (r', Void) | Alt (Void, r') -> 
      optimize_re r' 
  | Alt (r1, Alt (r2, r3)) -> 
      alt (alt (optimize_re r1) (optimize_re r2)) (optimize_re r3)
  | Alt (r1, r2) when equal_re r1 r2 -> 
      optimize_re r1 
  | Star Void | Star Epsilon -> 
      Epsilon 
  | Star (Star r') -> 
      optimize_re @@ star r'
  | _ -> r

(** Another version of [optimize_re] which just calls the
   smart constructor  *)
let rec optimize_re' (r : re) : re = 
  match r with 
  | Seq (r1, r2) -> seq (optimize_re' r1) (optimize_re' r2)
  | Alt (r1, r2) -> alt (optimize_re' r1) (optimize_re' r2) 
  | Star r' -> star (optimize_re' r')
  | _ -> r

(** Determines if a regex contains [Void] *)  
let rec contains_void (r : re) : bool = 
  match r with 
  | Void -> true 
  | Alt (r1, r2) | Seq (r1, r2) -> contains_void r1 || contains_void r2 
  | Star r' -> contains_void r' 
  | _ -> false  
  
  
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
let regex_set_map (f : re -> re) (rs : RegexSet.t) : RegexSet.t = 
  RegexSet.fold (fun r -> RegexSet.add (f r)) rs RegexSet.empty

(** Computes the max height of a regex in a set of regexes [rs] *)
let max_height_re_set (rs : RegexSet.t) : int = 
  RegexSet.fold (fun r acc -> max (re_height r) acc) rs 0
