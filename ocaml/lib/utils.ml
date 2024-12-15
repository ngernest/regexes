open Regex 
open Antimirov
open Extracted_brzozowski_zipper

(** Represents a regex as a string using infix notation *)
let rec string_of_re (r : re) : string = 
  let open Printf in 
  match r with 
  | Void -> "⊥"
  | Epsilon -> "ε"
  | Atom c -> sprintf "%c" c
  | Concat (r1, r2) -> sprintf "(%s ⋅ %s)" (string_of_re r1) (string_of_re r2)
  | Union (r1, r2) -> sprintf "(%s + %s)" (string_of_re r1) (string_of_re r2)
  | Star r' -> sprintf "(%s)*" (string_of_re r')
  
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

(** Converts a list of [re] elements to a string *)    
let string_of_re_list (rs : re list) : string = 
  match rs with 
  | [] -> "∅"
  | _ -> let contents = Base.String.concat ~sep:"; " (List.map string_of_re rs) in 
    Printf.sprintf "{ %s }" contents

(** Converts a [RegexSet.t] to a string *)    
let string_of_regex_set (regex_set : RegexSet.t) : string = 
  let rs : re list = RegexSet.elements regex_set in 
  match rs with 
  | [] -> "∅"
  | _ -> Printf.sprintf "{ %s }" 
    (Base.String.concat ~sep:", " (List.map string_of_re rs)) 

(** Converts a [context] to a [re] *)
let context_to_re (ctx : context) : re = 
  List.fold_left seq Epsilon ctx 

(** Simplifies each element of a list of regexes using rewrite rules,
    sorts the resultant list and removes duplicates *)  
let postprocess_regex_list (rs : re list) : re list = 
  Base.List.dedup_and_sort ~compare:compare_re (List.map optimize_re rs)  

(** Checks whether a regex containing [Union]s is sorted (i.e. all the arguments 
    to [Union]s are sorted in increasing order wrt [compare_re]) *)  
let rec is_sorted (r : re) : bool = 
  match r with 
  | Union (r1, Union (r2, r3)) -> compare_re r1 r2 <= 0 && is_sorted (Union (r2, r3))
  | Union (r1, r2) -> is_sorted r1 && is_sorted r2 && compare_re r1 r2 <= 0
  | Concat (r1, r2) -> is_sorted r1 && is_sorted r2 
  | Star r' -> is_sorted r' 
  | _ -> true 

(** Computes the underlying set of regexes for the zipper corresponding
    to the Brzozowski derivative of [r] w.r.t. [c] *)
let underlying_zipper_set (r : re) (c : char) : re set = 
  zipper_map context_to_re (derive c (focus r))  
