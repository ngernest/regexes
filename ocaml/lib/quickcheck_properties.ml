open Regex 
open Antimirov 
open Brzozowski
open Extracted_brzozowski_zipper
open Base_quickcheck
open Sexplib.Conv

(* -------------------------------------------------------------------------- *)
(*                      QuickCheck Generators + Shrinkers                     *)
(* -------------------------------------------------------------------------- *)
   
(** Generates an optimized regex *)
let gen_optimized_re : re Generator.t = 
  let open Generator.Let_syntax in 
  quickcheck_generator_re >>| optimize_re'

(** Generator that generates a pair consisting of a regex 
    and an lowercase character *)
let gen_re_char : (re * char) Generator.t = 
  Generator.both gen_optimized_re Generator.char_lowercase

(** A shrinker for regexes:
    - All characters are shrunk to [Epsilon]
    - For [Star], [Seq], and [Alt], we shrink via structural recursion and 
      use the smart constructors to create shrunken regexes *)    
let shrink_re : re Shrinker.t = 
  let open Base in 
  let open Sequence.Let_syntax in 
  let rec aux (r : re) : re Sequence.t =
    begin match r with 
    | Epsilon | Void -> Sequence.empty 
    | Char _ -> Sequence.singleton Epsilon
    | Star r' -> Sequence.map ~f:star (aux r') 
    | Seq (r1, r2) -> 
      let%map r1' = aux r1 and r2' = aux r2 in seq r1' r2'
    | Alt (r1, r2) -> 
      let%map r1' = aux r1 and r2' = aux r2 in alt r1' r2'
    end
  in 
  Shrinker.create aux

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
  | None -> failwith @@ 
      Printf.sprintf "No string matches regex %s\n" 
      (Base.Sexp.to_string_hum (sexp_of_re r))
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
  Shrinker.both shrink_re Shrinker.char  

(** Generates a regex that consists of an [Alt] at the top-level *)  
let gen_alt : re Generator.t = 
  let open Generator.Let_syntax in 
  let%map r1 = gen_optimized_re and r2 = gen_optimized_re in 
  alt r1 r2        

(** Default QuickCheck config: 10000 trials *)  
let config : Base_quickcheck.Test.Config.t = 
  { Base_quickcheck.Test.default_config with 
    test_count = 10_000; 
    shrink_count = 10_000 }
    
(* -------------------------------------------------------------------------- *)
(*                       Helper functions for QuickCheck                      *)
(* -------------------------------------------------------------------------- *)

(** Converts a regex to a string *)
let string_of_re (r : re) : string = 
  Base.Sexp.to_string_hum (sexp_of_re r)  

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

let underlying_zipper_set (r : re) (c : char) : re list = 
  zipper_map context_to_re (derive c (focus r))  

(* -------------------------------------------------------------------------- *)
(*                            QuickCheck properties                           *)
(* -------------------------------------------------------------------------- *)

let%quick_test "alt smart constructor produces sorted regexes" = 
  fun (r : re [@generator gen_alt] [@shrinker shrink_re]) ->
    assert (is_sorted r);
  [%expect {| |}]

let%quick_test "Brzozowski & Antimirov-based regex matchers accept the same strings!" 
  [@generator gen_re_string] [@config config] = 
  fun (r : re) (s : string) -> 
    let antimirov_result = antimirov_match r s in 
    let brzozowski_result = brzozowski_match r s in 
    assert (Bool.equal antimirov_result brzozowski_result);
  [@expect {| |}]

let%quick_test {| The regex matchers based on Brzozowski derivatives & zippers 
  accept the same strings |}
  [@generator gen_re_string] [@config config] = 
  fun (r : re) (s : string) -> 
    let brzozowski_result = brzozowski_match r s in 
    let zipper_result = zipper_match r s in 
    assert (Bool.equal brzozowski_result zipper_result);
  [%expect {| |}]
  
let%quick_test "the zipper of a union is the union of the zippers" 
  [@config config] = 
  fun (r1 : re [@generator gen_optimized_re] [@shrinker shrink_re]) 
    (r2 : re [@generator gen_optimized_re] [@shrinker shrink_re]) 
    (c : char [@generator Generator.of_list ['a'; 'b']]) -> 
      let lhs = postprocess_regex_list @@ 
        underlying_zipper_set (Alt (r1, r2)) c in 
      let rhs = postprocess_regex_list @@ 
        ListSet.union (underlying_zipper_set r1 c) (underlying_zipper_set r2 c) in 
      assert (List.equal equal_re lhs rhs);
  [%expect {| |}]
  
let%quick_test "underlying sets for zippers & Antimirov are the same" 
  [@config config] = 
  fun (r : re [@generator gen_optimized_re] [@shrinker shrink_re]) 
    (c : char [@generator Generator.of_list ['a'; 'b']]) -> 
    let input = optimize_re' r in 
    let lhs = postprocess_regex_list (underlying_zipper_set r c) in 
    let rhs = postprocess_regex_list @@ 
      RegexSet.to_list (aderiv c r) in 
    let result = List.equal equal_re lhs rhs in 
    assert result;
  [%expect {| |}]    

let%quick_test {| flattening a zipper and flattening the Antimirov derivative set 
  result in equivalent regexes |}
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config] = 
  fun (r : re) (c : char) -> 
    let open Stdio in 
    let input = optimize_re' r in 
    let lhs = optimize_re' @@ flatten_zipper (derive c (focus r)) in 
    let rhs = optimize_re' @@ RegexSet.fold 
      (fun r' acc -> alt r' acc) (aderiv c r) Void in 
    let result = equal_re lhs rhs in 
    assert (not (contains_void r));
    assert result;
  [%expect {| |}]
  
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

let%quick_test ("Brzozowski is always contained in the set of Antimirov derivatives 
  (this property is falsified!)"
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config]) = 
  fun (r : re) (c : char) -> 
    assert (RegexSet.mem (Brzozowski.bderiv r c) (aderiv c r));
  [%expect {|
    ("quick test: test failed" (input (Epsilon T)))
    (* CR require-failed: lib/quickcheck_properties.ml:225:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:229:4"
    |}]

let%expect_test {| Example where a Brzozowski derivative is not contained in the set of Antimirov derivatives 
  (e.g. when the Brzozowski derivative is [Void] and the Antimirov derivative set is the empty set) |} = 
  let bderiv = Brzozowski.bderiv (Char 'b') 'T' in 
  Stdio.printf "%s\n" (string_of_re bderiv);
  [%expect {| Void |}]

let%quick_test ("Brzozowski contained in Antimirov set when it is non-empty 
  (this property is falsified!)"
  [@generator gen_re_char_nonempty_antimirov] [@config config]) =
  fun (r : re) (c : char) -> 
    let antimirov_set = aderiv_opt c r in 
    assert (RegexSet.mem (Brzozowski.bderiv_opt r c) antimirov_set);
  [%expect {|
    ("quick test: test failed" (input (Epsilon T)))
    (* CR require-failed: lib/quickcheck_properties.ml:245:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:250:4"
    |}]
  