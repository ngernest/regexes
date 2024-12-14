open Regex 
open Antimirov 
open Brzozowski
open Extracted_brzozowski_zipper
open Utils


let%expect_test "derive_up a [Void] " = 
  let z = derive_up 'a' [Void] in 
  Stdio.printf "%s\n" (string_of_zipper z);
  [%expect {| ∅ |}]

let%expect_test "" = 
  let r = context_to_re [Atom 'a'] in 
  Stdio.printf "%s\n" (string_of_re r);
  [%expect {| (Atom a) |}]
  

    