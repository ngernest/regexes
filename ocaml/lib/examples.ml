open Regex 
open Antimirov 
open Brzozowski
open Extracted_brzozowski_zipper
open Base_quickcheck
open Sexplib.Conv

(* TODO: complete this expect test *)

let%expect_test {| Example where a Brzozowski derivative is not contained in the set of Antimirov derivatives 
  (e.g. when the Brzozowski derivative is [Void] and the Antimirov derivative set is the empty set) |} = 
  let res = derive_up 'a' [Void] in ()
  