open Brzozowski
open Antimirov
open Extracted_brzozowski_zipper
open Quickcheck_properties
open Utils
open Core

let mk_accept_string (b : bool) : string = 
  if b then "accepted" else "rejected"

(** Generates 15 random (regex, string) pairs, and shows that the three regex 
    matchers respectively based on Brzozowski / Antimirov / zippers return the same 
    acceptance result *)  
let three_matchers_demo () = 
  Quickcheck.iter
    ~seed:(`Deterministic "hello")
    ~trials:15
    gen_re_string 
    ~f:(fun (r, s) -> 
      printf "r = %s\ns = \"%s\"\n" (string_of_re r) s;
      let brzozowski_res = brzozowski_match r s in 
      let antimirov_res = antimirov_match r s in 
      let zipper_res = zipper_match r s in 
      printf "Brzozowski matcher : %s\n" (mk_accept_string brzozowski_res);
      printf "Antimirov matcher  : %s\n" (mk_accept_string antimirov_res);
      printf "Zipper matcher     : %s\n" (mk_accept_string zipper_res);
      printf "***************************************\n")
