open Regex 
open Antimirov 
open Brzozowski
open Brzozowski_zipper
open Base_quickcheck
open Sexplib.Conv

(* -------------------------------------------------------------------------- *)
(*                      QuickCheck Generators + Shrinkers                     *)
(* -------------------------------------------------------------------------- *)
   
(** Generator that generates a pair consisting of a regex 
   and an lowercase character *)
let gen_re_char : (re * char) Generator.t = 
  Generator.both quickcheck_generator_re Generator.char_lowercase

(** Returns a generator that produces random strings matching the regex [r] 
    (if such a generator exists) *)  
let rec gen_regex_string (r : re) : (string Generator.t) option = 
  let open Generator in 
  let open Generator.Let_syntax in 
  match r with 
  | Void -> None
  | Epsilon -> Some (return "")
  | Char c -> Some (return (Base.Char.to_string c))
  | Alt (r1, r2) -> 
    begin match (gen_regex_string r1, gen_regex_string r2) with 
    | None, None -> None
    | Some g1, _ -> Some g1 
    | _, Some g2 -> Some g2
    end 
  | Seq (r1, r2) -> 
    begin match (gen_regex_string r1, gen_regex_string r2) with 
    | Some g1, Some g2 -> 
      Some (let%map s1 = g1 and s2 = g2 in s1 ^ s2)
    | _ -> None
    end 
  | Star r' -> 
    begin match gen_regex_string r' with 
    | None -> None 
    | Some g -> Some (
      (* iterate at most k times *)
      let%bind k = small_strictly_positive_int in 
      let%bind xs = list_with_length ~length:k g in  
      return @@ String.concat "" xs)
    end

(** Generates a pair consisting of a regex and a string which matches 
    that regex *)    
let gen_re_string : (re * string) Generator.t = 
  let open Generator.Let_syntax in 
  let%bind r = quickcheck_generator_re in 
  begin match gen_regex_string r with 
  | Some gen_string -> 
    let%bind s = gen_string in 
    Generator.return (r, s)
  | None -> failwith "TODO"
  end 
      

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

(* -------------------------------------------------------------------------- *)
(*                            QuickCheck properties                           *)
(* -------------------------------------------------------------------------- *)

let%quick_test "Brzozowski & Antimirov-based regex matchers accept the same strings!" 
  [@generator gen_re_string] [@config config] = 
  fun (r : re) (s : string) -> 
    let antimirov_result = antimirov_match r s in 
    let brzozowski_result = brzozowski_match r s in 
    assert (Bool.equal antimirov_result brzozowski_result);
  [@expect {| |}]

let%quick_test "Brzozowski derivative & zippers accept the same strings" 
  [@generator gen_re_string] [@config config] = 
  fun (r : re) (s : string) -> 
    let brzozowski_result = brzozowski_match r s in 
    let zipper_result = zipper_match (regex_of_re r) s in 
    assert (Bool.equal brzozowski_result zipper_result);
  [@expect {| |}];
  [%expect {|
    ("quick test: test failed" (input (Epsilon 4)))
    (* CR require-failed: lib/quickcheck_properties.ml:90:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:95:4"
    |}]
    
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
    (* CR require-failed: lib/quickcheck_properties.ml:123:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:127:4"
    |}]

let%expect_test {| Example where a Brzozowski derivative is not contained in the set of Antimirov derivatives 
  (e.g. when BRzozowski derivative is [Void] and the Antimirov derivative set is the empty set) |} = 
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
    (* CR require-failed: lib/quickcheck_properties.ml:144:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:149:4"
    |}]
  
