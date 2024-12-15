(******************************************************************************)
(** Boilerplate to make the extracted code more usable *)

open Regex

(** Finite sets implemented using lists, adapted from CS 3110 *)
module ListSet = struct
  type 'a t = 'a list

  let empty = []
  let is_empty = function [] -> true | _ -> false
  let mem x lst = List.mem x lst
  let add x s = if mem x s then s else x :: s
  let rem x = List.filter (( <> ) x)
  let dedup lst = lst |> List.sort_uniq Stdlib.compare
  let size s = s |> dedup |> List.length
  let union s1 s2 = s1 @ s2 |> dedup
  let intersect lst1 lst2 = List.filter (fun h -> mem h lst2) lst1

  let map = List.map
end

(******************************************************************************)
(** Code below is extracted from the Coq code in [Edelmann.v] 
    (lightly modified to use the functions from the [ListSet] module above) *)

type 'a set = 'a list

(** Checks if a regex accepts the empty string *)  
let rec nullable : re -> bool = function
  | Void -> false
  | Atom _ -> false
  | Union (l, r) -> if nullable l then true else nullable r
  | Concat (l, r) -> if nullable l then nullable r else false
  | _ -> true

(** A [context] is a list of [regex]es. 
  Semantically, these represent {i sequences} of regexes, specifically 
  all regexes that come after the focal point. *)
type context = re list

(** A [zipper] is a set of [context]s, 
    i.e. [Zipper.t = context Set.t = (regex list) Set.t]. 
    Semantically, zippers represent {i disjunctions} of lists of regexes 
    that arise when deriving. *)
type zipper = context set

(** Maps a function over a zipper, returning a new set *)
let zipper_map (f : context -> 'a) (z : zipper) : 'a set = 
  ListSet.map f z

(** Takes the union of two zippers *)  
let zipper_union : zipper -> zipper -> zipper = 
  ListSet.union 

(** Creates a zipper from a regex *)      
let focus (e : re) : zipper = [[e]]

(** Moves the focus down the regex. 
    - When a context matches an [Atom], we collect them in a set
      and form the resulting [zipper] using this set *)
let rec derive_down (c : char) (e : re) (ctx : context) : zipper =
  match e with
  | Atom cl -> if Char.equal cl c then ctx::[] else []
  | Union (l, r) ->
    zipper_union (derive_down c l ctx) (derive_down c r ctx)
  | Concat (l, r) ->
    if nullable l
    then zipper_union (derive_down c l (r::ctx)) (derive_down c r ctx)
    else derive_down c l (r::ctx)
  | Star e' -> derive_down c e' (e::ctx)
  | _ -> []

(** Move the focus up the regex to all subterms that can be reached without 
    consuming any input:
    - [derive_up] stops processing when it reaches a non-nullable regex *)
let rec derive_up (c : char) (ctx : context) : zipper = 
  match ctx with
  | [] -> []
  | e::ctx' ->
    if nullable e
    then zipper_union (derive_down c e ctx') (derive_up c ctx')
    else derive_down c e ctx'

(** Variant of Brzozowski derivatives for zippers *)
let derive (c : char) (z : zipper) : zipper =
  List.fold_left zipper_union [] (List.map (derive_up c) z)

(** Derives by all characters in the argument [char list] *)  
let rec derive_word (w : char list) (z : zipper) : zipper =
  match w with
  | [] -> z
  | c::w' -> derive_word w' (derive c z)

(** To check if a [zipper] accepts the empty string,
    check if it contains a context that only consists of nullable regexes *)  
let zipper_nullable (z : zipper) : bool =
  List.exists (fun ctx -> List.for_all nullable ctx) z

(** Checks whether a string matches a regex using zippers 
    (converts the regex into a zipper using [focus], computes 
    its derivative over the string, and then checks whether 
    the resultant zipper accepts the empty string) *)  
let zipper_accepts (z : zipper) (w : char list) : bool =
  zipper_nullable (derive_word w z)

(** Determines whether a string matches a regex using zippers *)  
let accepts (e : re) (w : char list) : bool =
  zipper_accepts (focus e) w

(** Determines whether a string matches a regex using zippers *)
let zipper_match (r : re) (s : string) : bool = 
  accepts r (Base.String.to_list s)

(** Converts a zipper to an equivalent regex *)
let flatten_zipper (z : zipper) : re = 
  List.fold_left 
    (fun acc ctx -> alt acc 
      (List.fold_left (fun acc' r -> seq acc' r) Epsilon ctx)) 
    Void z
