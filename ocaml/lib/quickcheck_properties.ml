open Regex 
open Antimirov 
open Brzozowski
open Extracted_brzozowski_zipper
open Base_quickcheck
open Sexplib.Conv

(* -------------------------------------------------------------------------- *)
(*                      QuickCheck Generators + Shrinkers                     *)
(* -------------------------------------------------------------------------- *)
   
(** Generator that generates a pair consisting of a regex 
    and an lowercase character *)
let gen_re_char : (re * char) Generator.t = 
  Generator.both (Generator.map quickcheck_generator_re ~f:optimize_re) 
    Generator.char_lowercase

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
  Shrinker.both quickcheck_shrinker_re Shrinker.char  

(** Default QuickCheck config: 10000 trials *)  
let config : Base_quickcheck.Test.Config.t = 
  { Base_quickcheck.Test.default_config with 
    test_count = 10_000_000; 
    shrink_count = 10_000_000 }


let string_of_re (r : re) : string = 
  Base.Sexp.to_string_hum (sexp_of_re r)  

(* -------------------------------------------------------------------------- *)
(*                            QuickCheck properties                           *)
(* -------------------------------------------------------------------------- *)

(* 

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



let%expect_test "counterexample" = 
  let r = Alt (
     Alt (Epsilon, Char 'k'), 
     Star (Seq (Alt (Void, Char 'k'), Seq (Epsilon, Void)))
  ) in 
  let c = 'k' in 
  let input = optimize_re' r in 
  let lhs = optimize_re' @@ flatten_zipper (derive c (focus r)) in 
  let rhs = optimize_re' @@ RegexSet.fold (fun r' acc -> alt r' acc) (aderiv c r) Void in 
  let result = equal_re lhs rhs in 
  Stdio.printf "optimized input = %s\n" (string_of_re input);
  Stdio.printf "lhs = %s\n" (string_of_re lhs);
  Stdio.printf "rhs = %s\n" (string_of_re rhs);
  Stdio.printf "result = %b\n" result;
  [@expect {| |}];
  [%expect {|
    optimized input = (Alt Epsilon (Alt (Char k) Epsilon))
    lhs = Epsilon
    rhs = Epsilon
    result = true
    |}]

let%expect_test "counterexample 2" = 
  let r = (Alt (Char '\135', (Seq ((Star (Alt (Char 'W', (Star (Char '1'))))), (Char 'W'))))) in 
  let c = 'W' in 
  let input = optimize_re' r in 
  let lhs = optimize_re' @@ flatten_zipper (derive c (focus r)) in 
  let rhs = optimize_re' @@ RegexSet.fold (fun r' acc -> alt r' acc) (aderiv c r) Void in 
  let result = equal_re lhs rhs in 
  Stdio.printf "optimized input = %s\n" (string_of_re input);
  Stdio.printf "lhs = %s\n" (string_of_re lhs);
  Stdio.printf "rhs = %s\n" (string_of_re rhs);
  Stdio.printf "result = %b\n" result;
  [@expect {| |}];
  [%expect {|
    optimized input = (Alt (Char "\135") (Seq (Star (Alt (Char W) (Star (Char 1)))) (Char W)))
    lhs = (Alt Epsilon (Seq (Star (Alt (Char W) (Star (Char 1)))) (Char W)))
    rhs = (Alt Epsilon (Seq (Star (Alt (Char W) (Star (Char 1)))) (Char W)))
    result = true
    |}]

*)    

(* let%expect_test "counterexample 3" = 
  let r = (Alt (
    (Star Epsilon),
    (Alt (
      (Seq (
        (Seq (
          (Star (
            Seq (
              (Alt (Void, (
                Seq (
                  (Seq (
                    (Alt ((Char '3'), (Star (Star Epsilon)))),
                    (Star (
                      Alt (
                        (Char 'U'),
                        (Char 'G')))))),
                  (Star (
                    Alt (
                      (Seq ((Char 'T'), (Star (Star (Alt ((Char 'H'), Epsilon)))))),
                      (Alt (
                        (Seq (
                          (Alt ((Seq ((Char '3'), (Star (Char '\201')))), (Star Void))),
                          (Char 't'))),
                        Epsilon)))))))),
              (Seq (Epsilon, Epsilon))))),
          (Star (Star Void)))),
        (Alt (
          (Alt (
            (Alt ((Char '3'), (Alt ((Seq (Epsilon, (Star Epsilon))), Epsilon)))),
            (Char 'o'))),
          (Seq (
            (Alt (
              (Char 'A'),
              (Star Epsilon))),
            Void)))))),
      (Char 'V')))))) in 
  let c = 'W' in 
  let input = optimize_re' r in 
  let lhs = optimize_re' @@ flatten_zipper (derive c (focus input)) in 
  let rhs = optimize_re' @@ RegexSet.fold (fun r' acc -> alt r' acc) (aderiv c input) Void in 
  let result = equal_re lhs rhs in 
  Stdio.printf "optimized input = %s\n" (string_of_re input);
  Stdio.printf "lhs = %s\n" (string_of_re lhs);
  Stdio.printf "rhs = %s\n" (string_of_re rhs);
  Stdio.printf "result = %b\n" result;
  [@expect {| |}];
  [%expect {|
    optimized input = (Alt Epsilon
     (Alt (Char V)
      (Seq
       (Star
        (Seq (Seq (Alt (Char 3) Epsilon) (Star (Alt (Char G) (Char U))))
         (Star
          (Alt (Seq (Char T) (Star (Alt (Char H) Epsilon)))
           (Alt Epsilon
            (Seq (Alt Epsilon (Seq (Char 3) (Star (Char "\201")))) (Char t)))))))
       (Alt (Char o) (Alt (Char 3) (Alt Epsilon Epsilon))))))
    lhs = Void
    rhs = Void
    result = true
    |}] 
    
  *)

let rec contains_void (r : re) : bool = 
  match r with 
  | Void -> true 
  | Alt (r1, r2) | Seq (r1, r2) -> contains_void r1 || contains_void r2 
  | Star r' -> contains_void r' 
  | _ -> false

(* 

Alternatively, we could just prove the following (gset equality):
(TODO: you may want to check that this property holds in QuickCheck for now)

Set.map context_to_re (derive c (focus r)) = aderiv c r
  where 
    context_to_re (ctx : context) : re = List.fold_left (fun acc r -> Seq (acc, r)) ctx 
*)  

 
let%quick_test {| flattening a zipper and flattening the Antimirov derivative set 
  result in equivalent regexes |}
  [@generator gen_re_char] [@shrinker shrink_re_char] [@config config] = 
  fun (r : re) (c : char) -> 
    let open Stdio in 
    let input = optimize_re' r in 
    let lhs = optimize_re' @@ flatten_zipper (derive c (focus r)) in 
    let rhs = optimize_re' @@ RegexSet.fold (fun r' acc -> alt r' acc) (aderiv c r) Void in 
    let result = equal_re lhs rhs in 
    assert (not (contains_void r));
    assert result;
  [%expect {| |}]
  

(* 

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
    ("quick test: test failed" (input ((Char b) T)))
    (* CR require-failed: lib/quickcheck_properties.ml:183:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:187:4"
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
    ("quick test: test failed" (input ((Char b) T)))
    (* CR require-failed: lib/quickcheck_properties.ml:203:0.
       Do not 'X' this CR; instead make the required property true,
       which will make the CR disappear.  For more information, see
       [Expect_test_helpers_base.require]. *)
    "Assert_failure lib/quickcheck_properties.ml:208:4"
    |}]
  
*)    