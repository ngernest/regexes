(** A regex matcher based on Antimirov derivatives, adapted from Neel Krishnaswami
    https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regulaRegexSet.html *)

open Regex
open Base_quickcheck
open Sexplib.Conv

(** [aderiv c r] is the Antimirov derivative of the regex [r] with respect 
    to the character [c]. This returns a set of partial derivatives, which 
    collectively accept the same strings as the Brzozowski derivative. *)
let rec aderiv (c : char) (r : re) : RegexSet.t = 
  match r with
  | Atom c' when c = c' -> RegexSet.singleton Epsilon 
  | Atom _ | Epsilon | Void -> RegexSet.empty
  | Union (r, r') -> RegexSet.union (aderiv c r) (aderiv c r')
  | Concat (r1, r2) -> RegexSet.union (regex_set_map (fun r1' -> Concat (r1', r2)) (aderiv c r1))
                           (if accepts_empty r1 then aderiv c r2 else RegexSet.empty)
  | Star r -> regex_set_map (fun r' -> Concat (r', Star r)) (aderiv c r)

(** Optimized version of [aderiv] which uses smart constructors *)  
let rec aderiv_opt (c : char) (r : re) : RegexSet.t = 
  match r with
  | Atom c' when c = c' -> RegexSet.singleton Epsilon 
  | Atom _ | Epsilon | Void -> RegexSet.empty
  | Union (r, r') -> RegexSet.union (aderiv_opt c r) (aderiv_opt c r')
  | Concat (r1, r2) -> RegexSet.union (regex_set_map (fun r1' -> seq r1' r2) (aderiv_opt c r1))
                    (if accepts_empty r1 then aderiv_opt c r2 else RegexSet.empty)
  | Star r -> regex_set_map (fun r' -> seq r' (star r)) (aderiv_opt c r)
  
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
