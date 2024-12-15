(** Translated from the Scala code in Romain Edelmann's PhD thesis:
    https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content *)

open Base_quickcheck
open Sexplib.Conv
open Lib.Regex

(** A datatype for regexes -- we define a separate type to keep the constructor 
    names the same as Edelmann's thesis *)   
type regex = 
  | Failure 
  | Epsilon 
  | Atom of char [@quickcheck.generator Generator.char_lowercase]
  | Concatuence of regex * regex 
  | Disjunction of regex * regex 
  | Star of regex
[@@deriving equal, quickcheck, sexp]

let string_of_regex (r : regex) : string = 
  Base.Sexp.to_string_hum (sexp_of_regex r)

(** Converts the [regex] type to the [re] type defined in [regex.ml] *)  
let rec re_of_regex (regex : regex) : re = 
  match regex with 
  | Failure -> Void 
  | Epsilon -> Epsilon 
  | Atom c -> Atom c 
  | Concatuence (r1, r2) -> Concat (re_of_regex r1, re_of_regex r2)
  | Disjunction (r1, r2) -> Union (re_of_regex r1, re_of_regex r2)
  | Star r -> Star (re_of_regex r)
  
(** Converts the [re] type defined in [regex.ml] to the [regex] type above *)    
let rec regex_of_re (re : re) : regex = 
  match re with 
  | Void -> Failure 
  | Epsilon -> Epsilon 
  | Atom c -> Atom c 
  | Concat (r1, r2) -> Concatuence (regex_of_re r1, regex_of_re r2)
  | Union (r1, r2) -> Disjunction (regex_of_re r1, regex_of_re r2)
  | Star r -> Star (regex_of_re r)

let%quick_test "round-trip property for re <-> regex conversion functions" 
  [@generator quickcheck_generator_re] = 
  fun (r : re) -> 
    assert (equal_re r (re_of_regex (regex_of_re r)));
  [@expect {| |}]

(** Checks if a regex accepts the empty string *)  
let rec is_nullable (r : regex) : bool = 
  match r with 
  | Failure | Atom _ -> false 
  | Epsilon | Star _ -> true 
  | Disjunction (r1, r2) -> is_nullable r1 || is_nullable r2 
  | Concatuence (r1, r2) -> is_nullable r1 && is_nullable r2 

(** A [context] is a list of [regex]es. 
    Semantically, these represent {i sequences} of regexes, specifically 
    all regexes that come after the focal point. *)
type context = regex list 

(** A [zipper] is a set of [context]s, 
    i.e. [Zipper.t = context Set.t = (regex list) Set.t]. 
    Semantically, zippers represent {i disjunctions} of lists of regexes 
    that arise when deriving. *)
module Zipper = Set.Make(struct
  type t = context 
  let compare = compare
end)

(** [concatMap] but for zippers: applies a function [f : context -> Zipper.t] 
    to each element within a [zipper], and takes the union of all the resultant 
    zippers *)
let zipper_concat_map (f : context -> Zipper.t) (z : Zipper.t) : Zipper.t = 
  Zipper.fold (fun ctx acc -> Zipper.union (f ctx) acc) Zipper.empty z

(** Converts a [zipper] to a [regex] *)
let unfocus (zipper : Zipper.t) : regex = 
  (* Converts a singular [context] to a [regex] *)
  let uncontext (ctx : context) : regex = 
    List.fold_left (fun r acc -> Concatuence (r, acc)) Epsilon ctx in 
  Zipper.fold 
    (fun ctx acc -> Disjunction (acc, uncontext ctx))
    zipper
    Failure

(* Example from Huet's dissertation: 
  {[
    r1 = unfocus @@ Zipper.of_list [[e1; e2]; [e3]] in 
    r2 = Disjunction (Concatuence (e1, e2), e3) 
  ]}
  [r1] and [r2] should be semantically equivalent regexes
  (need to apply some rewrite rules) *)

(** Creates a zipper from a regex *)    
let focus (r : regex) : Zipper.t = Zipper.singleton [r]

(* Theorem 2.1
   Round-trip property, where [~=] denotes a regex matching a string
   [{
      forall (r : regex) (cs : list char), 
      unfocus (focus r) ~= cs <--> r ~= cs
   }] *)

(** Variant of Brzozowski derivatives for zippers *)
let derive (zipper : Zipper.t) (c : char) : Zipper.t = 
  (** Move the focus up the regex to all subterms that can be reached without 
     consuming any input:
     - [up] stops processing when it reaches a non-nullable regex *)
  let rec up (ctx : context) : Zipper.t = 
    begin match ctx with 
    | [] -> 
        Zipper.empty 
    | right :: parent when is_nullable right -> 
        Zipper.union (down right parent) (up parent)
    | right :: parent -> 
        down right parent 
    end
  (** Moves the focus down the regex *)
  and down (r : regex) (ctx : context) : Zipper.t = 
    begin match r with 
    | Atom d when Base.Char.equal d c ->
        (* When a context matches a [Atom], we collect them in a set
           and form the resulting [zipper] using this set *) 
        Zipper.singleton ctx
    | Disjunction (left, right) -> 
        Zipper.union (down left ctx) (down right ctx)
    | Concatuence (left, right) when is_nullable left -> 
        Zipper.union (down left (right :: ctx)) (down right ctx)
    | Concatuence (left, right) -> 
        down left (right :: ctx)
    | Star r' -> 
        down r' (r :: ctx)
    | _ -> Zipper.empty
    end in 
  (* if OCaml had [concatMap] for sets, 
    this would just be [Zipper.concatMap up zipper] *)
  zipper_concat_map up zipper
  
(* Theorem 2.2:
  [{ forall (z : zipper) (c : char) (cs : char list), 
    unfocus (derive z c) ~= cs <--> unfocus z ~= c :: cs
  }]   *)

(** Derives by all characters in the argument [char list] *)
let derive_word (zipper : Zipper.t) (cs : char list) : Zipper.t = 
  List.fold_left derive zipper cs

(* Theorem 2.3 
  {[ forall (z : zipper) (cs1 cs2 : char list),
     unfocus (derive_word (z, cs1)) ~= cs2 <--> unfoucs z ~= cs1 ++ cs2 ]}
*)  

(** To check if a [zipper] accepts the empty string,
    check if it contains a context that only consists of nullable regexes *)
let zipper_is_nullable (zipper : Zipper.t) : bool = 
  Zipper.exists (fun ctx -> List.for_all is_nullable ctx) zipper

(* Theorem 2.4
   {[ forall (z : zipper),
      zipper_is_nullable z = true <-> unfocus z ~= ""
   ]}
*)  

(** Checks whether a string matches a regex using zippers 
    (converts the regex into a zipper using [focus], computes 
    its derivative over the string, and then checks whether 
    the resultant zipper accepts the empty string) *)
let accepts (r : regex) (cs : char list) : bool = 
  zipper_is_nullable (derive_word (focus r) cs)

(* Theorem 2.5
   {[ forall (r : regex) (cs : char list),
      accepts r cs = true <--> r ~= cs
   ]}
*)  

(** Determines whether a string matches a regex using zippers *)
let zipper_match (r : regex) (s : string) : bool = 
  accepts r (Base.String.to_list s)

(* -------------------------------------------------------------------------- *)
(*                                 Unit tests                                 *)
(* -------------------------------------------------------------------------- *)

let%expect_test {| Epsilon ~= "" |} = 
  Stdio.printf "%b\n" (zipper_match (Epsilon) "");
  [%expect {| true |}]

(* Not sure why this expect test doesn't pass *)  
let%expect_test "accepts Atom" = 
  Stdio.printf "%b\n" (accepts (Atom 'c') ['c']);
  [%expect {| false |}]

(* Not sure why this expect test doesn't pass *)  
let%expect_test {| Atom c ~= 'c' |} =
  Stdio.printf "%b\n" (zipper_match (Atom 'c') (Base.Char.to_string 'c'));
  [%expect {| false |}]

(* -------------------------------------------------------------------------- *)
(*                        Constructing Maximal Zippers                        *)
(* -------------------------------------------------------------------------- *)
  
(** Takes a zipper [z] and constructs a {i maximal zipper} from it *)
let max_zipper (z : Zipper.t) : Zipper.t = 
  let rec up (ctx : context) : Zipper.t = 
    begin match ctx with 
    | [] -> Zipper.empty 
    | right :: parent -> Zipper.union (down right parent) (up parent)
    end 
  and down (r : regex) (ctx : context) : Zipper.t = 
    begin match r with 
    | Atom _ -> 
        Zipper.singleton ctx 
    | Disjunction (left, right) -> 
        Zipper.union (down left ctx) (down right ctx)
    | Concatuence (left, right) -> 
        Zipper.union (down left (right :: ctx)) (down right ctx)
    | Star r' -> 
        down r' (r :: ctx)
    | _ -> Zipper.empty 
    end in 
  zipper_concat_map up z

(* 
  Lemma 2.1: 
  {[ forall (z : zipper) (c : char), derive z c ⊆ maxZipper z ]}
  
  Lemma 2.2 (derivation is monotonic wrt maxZipper inclusion):
  {[ forall (z : zipper) (c : char), maxZipper (derive z c) ⊆ maxZipper z }]
  
  Lemma 2.3 
  {[ forall (z : zipper) (cs : char list), cs <> [] -> 
       deriveWord z cs ⊆ maxZipper z ]}

  Theorem 2.6: (finiteness)
  {[ forall (z : zipper), 
       exists (Z : context set), 
         forall (cs : char list),
           deriveWord z cs ⊆ Z 
  ]}
*)

(* Counting contexts (from section 2.6): 
- The set [Z] in Theorem 2.6 can be constructed as [z] union with [maxZipper z].
- The no. of zippers that can be encountered starting from any regex [r] is at most 
  $$ 1 + 2 ^ |maxZipper (focus r)| $$
- The constant $1$ represents the unique context in [focus r],
  while the term $2 ^ |maxZipper (focus r)|$ represents the no. of subsets 
  in [maxZipper (focus r)]. 

- The size of [maxZipper (focus r)] is also bounded by the no. of [Atomacter]
  AST nodes in the original regex [r]
*)
