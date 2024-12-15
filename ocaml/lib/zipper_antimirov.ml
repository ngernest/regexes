open Regex
open Extracted_brzozowski_zipper
open Antimirov
open Quickcheck_properties
open Utils

(* Converts a [context] (used in Edelmann's zipper representation) to a regex 
   by folding the [concat] smart constructor over the context *)
let context_to_re (ctx : context) : re = 
  List.fold_left Regex.seq Epsilon ctx

(** The underlying regex set that forms Edelmann's zipper representation of 
   Brozozwski derivatives *)  
let underlying_zipper_set (r : re) (c : char) : re list = 
  zipper_map context_to_re (derive c (focus r))  

(** The underlying regex set formed after taking the Antimirov derivative *)  
let underlying_antimirov_set (r : re) (c : char) : RegexSet.t = 
  aderiv c r

(** Generates 15 random (regex, char) pairs, and shows that the underlying
    regex sets for both Antimirov & zippers are the same *)
let zipper_antimirov_demo () = 
  let open Core in 
  Quickcheck.iter 
    ~seed:(`Deterministic "2024_regex_project")
    ~trials:15
    (Quickcheck.Generator.filter gen_re_char 
      ~f:(fun (r, c) -> not @@ List.is_empty (underlying_zipper_set r c)))
    ~f:(fun (r, c) ->
      printf "r = %s \nc = %c\n" (string_of_re r) c;
      let zset = List.map ~f:optimize_re (underlying_zipper_set r c) in 
      let aset = RegexSet.map optimize_re (underlying_antimirov_set r c) in 
    printf "Zippers   : %s\n" (string_of_re_list zset);
    printf "Antimirov : %s\n" (string_of_regex_set aset);
    printf "***************************************\n")
