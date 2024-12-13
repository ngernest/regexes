open Regex 
open Extracted_brzozowski_zipper

(** Converts a regex to a string *)
let string_of_re (r : re) : string = 
  Base.Sexp.to_string_hum (sexp_of_re r) 
  
(** Converts a [context] to a string *)
let string_of_ctx (ctx : context) : string = 
  match ctx with 
  | [] -> "[]"
  | rs -> 
    let contents = Base.String.concat ~sep:"; " (List.map string_of_re rs) in 
    Printf.sprintf "[ %s ]" contents

(** Converts a [zipper] to a string *)  
let string_of_zipper (z : zipper) : string = 
  match z with 
  | [] -> "∅"
  | ctxs -> Printf.sprintf "{ %s }" 
    (Base.String.concat ~sep:", " (List.map string_of_ctx ctxs)) 

(** Converts a [context] to a [re] *)
let context_to_re (ctx : context) : re = 
  List.fold_left seq Epsilon ctx 

(** Simplifies each element of a list of regexes using rewrite rules,
    sorts the resultant list and removes duplicates *)  
let postprocess_regex_list (rs : re list) : re list = 
  Base.List.dedup_and_sort ~compare:compare_re (List.map optimize_re' rs)  

(** Checks whether a regex containing [Alt]s is sorted (i.e. all the arguments 
    to [Alt]s are sorted in increasing order wrt [compare_re]) *)  
let rec is_sorted (r : re) : bool = 
  match r with 
  | Alt (r1, Alt (r2, r3)) -> compare_re r1 r2 <= 0 && is_sorted (Alt (r2, r3))
  | Alt (r1, r2) -> is_sorted r1 && is_sorted r2 && compare_re r1 r2 <= 0
  | Seq (r1, r2) -> is_sorted r1 && is_sorted r2 
  | Star r' -> is_sorted r' 
  | _ -> true 

(** Computes the underlying set of regexes for the zipper corresponding
    to the Brzozowski derivative of [r] w.r.t. [c] *)
let underlying_zipper_set (r : re) (c : char) : re set = 
  zipper_map context_to_re (derive c (focus r))  
