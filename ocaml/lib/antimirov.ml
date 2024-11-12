(* A regex matcher based on Antimirov derivatives, 
   adapted from Neel Krishnaswami
   https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regulaRegexSet.html *)
open Regex
open Base_quickcheck
open Sexplib.Conv

(** [aderiv c r] is the Antimirov derivative of the regex [r] with respect 
    to the character [c]. This returns a set of partial derivatives, which 
    collectively accept the same strings as the Brzozowski derivative. *)
let rec aderiv (c : char) (r : re) : RegexSet.t = 
  match r with
  | Char c' when c = c' -> RegexSet.singleton Epsilon 
  | Char _ | Epsilon | Void -> RegexSet.empty
  | Alt (r, r') -> RegexSet.union (aderiv c r) (aderiv c r')
  | Seq (r1, r2) -> RegexSet.union (rmap (fun r1' -> Seq (r1', r2)) (aderiv c r1))
                           (if accepts_empty r1 then aderiv c r2 else RegexSet.empty)
  | Star r -> rmap (fun r' -> Seq (r', Star r)) (aderiv c r)

(** Optimized version of [aderiv] which uses smart constructors *)  
let rec aderiv_opt (c : char) (r : re) : RegexSet.t = 
  match r with
  | Char c' when c = c' -> RegexSet.singleton Epsilon 
  | Char _ | Epsilon | Void -> RegexSet.empty
  | Alt (r, r') -> RegexSet.union (aderiv_opt c r) (aderiv_opt c r')
  | Seq (r1, r2) -> RegexSet.union (rmap (fun r1' -> seq r1' r2) (aderiv_opt c r1))
                    (if accepts_empty r1 then aderiv_opt c r2 else RegexSet.empty)
  | Star r -> rmap (fun r' -> seq r' (star r)) (aderiv_opt c r)
  
(** Applies the Antimirov derivative to a whole set of regexes, 
    and takes the union *)
let aderiv' (c : char) (rs : RegexSet.t) : RegexSet.t = 
  RegexSet.fold (fun r acc -> RegexSet.union (aderiv c r) acc) rs RegexSet.empty

(** Checks whether there exists a regex inside the set [rs] which
    accepts the empty string *)  
let set_accepts_empty (rs : RegexSet.t) : bool = 
  RegexSet.exists accepts_empty rs

(** Uses Antimirov derivatives to determine whether the string [s] 
  matches the regex [r] *)  
let antimirov_match (r : re) (s : string) : bool = 
  set_accepts_empty (String.fold_left 
    (fun rs c -> aderiv' c rs) (RegexSet.singleton r) s)  

(* -------------------------------------------------------------------------- *)
(*                      Experiments with QuickCheck                           *)
(* -------------------------------------------------------------------------- *)
   
(** Generator that generates a pair consisting of a regex 
   and an lowercase character *)
let gen_re_char : (re * char) Generator.t = 
  Generator.both quickcheck_generator_re Generator.char_lowercase

(** Only generates pairs of regexes and chars for which the set of 
  Antimirov derivatives is non-empty *)  
let gen_re_char_nonempty_antimirov : (re * char) Generator.t = 
  Generator.filter gen_re_char 
    ~f:(fun (r, c) -> 
      let antimirov_set = aderiv_opt c r in 
      RegexSet.cardinal antimirov_set > 0 && 
      not (RegexSet.is_empty antimirov_set))

(** Shrinker that shrinkers both a regex and an alphabetic character *)  
let shrink_re_char : (re * char) Shrinker.t = 
  Shrinker.both quickcheck_shrinker_re Shrinker.char  

(** Default QuickCheck config: 10000 trials *)  
let config : Base_quickcheck.Test.Config.t = 
  Base_quickcheck.Test.default_config

(* Technically, the lemma statement is that the no. of Antimirov deriatives
   is linear in the regex size, but there's no way to express 
  existential quantification in OCaml's QuickCheck library, so we 
  use QC to test a weaker version of this lemma (which just says
  the no. of Antimirov derivatives is upper-bounded by the regex size) *)  
let%quick_test ("No. of Antimirov derivatives is at most the size of the regex" 
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config]) =
  fun (r : re) (c : char) -> 
    assert (RegexSet.cardinal (aderiv c r) <= re_size r);
  [%expect {| |}]
  
let%quick_test ("Max height of any Antimirov derivative <= 2 * re_height"
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config]) = 
  fun (r : re) (c : char) -> 
    assert (max_height_re_set (aderiv c r) <= 2 * re_size r);
  [%expect {| |}]

let%quick_test ("Brzozowski is always contained in the set of Antimirov deriv 
  (this property is falsified!)"
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config]) = 
  fun (r : re) (c : char) -> 
    assert (RegexSet.mem (Brzozowski.bderiv r c) (aderiv c r));
  [%expect.unreachable];
  [%expect {|
    ("quick test: test failed" (input ((Char b) T)))
    (* CR require-failed: lib/antimirov.ml:352:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappeaRegexSet.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/antimirov.ml:355:4"
    |}]

let%expect_test "Example where Brzozowski is not contained in Antimirov" = 
  let bderiv = Brzozowski.bderiv (Char 'b') 'T' in 
  Stdio.printf "%s\n" (Base.Sexp.to_string_hum (sexp_of_re bderiv));
  [%expect {| Void |}]

let%quick_test ("Brzozowski contained in Antimirov set when it is non-empty 
  (this property is falsified!)"
  [@generator gen_re_char_nonempty_antimirov] [@config config]) =
  fun (r : re) (c : char) -> 
    let antimirov_set = aderiv_opt c r in 
    assert (RegexSet.mem (Brzozowski.bderiv_opt r c) antimirov_set);
  [%expect {|
    ("quick test: test failed" (input ((Char b) T)))
    (* CR require-failed: lib/antimirov.ml:371:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappeaRegexSet.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/antimirov.ml:376:4"
    |}]
  

  

    