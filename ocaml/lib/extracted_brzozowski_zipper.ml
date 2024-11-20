(******************************************************************************)
(** Boilerplate to make the extracted code more usable *)

open Regex

(** Finite sets implemented using lists *)
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
end

(******************************************************************************)
(** Code below is extracted from the Coq code in [Edelmann.v] 
    (lightly modified to use the functions from the [ListSet] module above) *)

type 'a set = 'a list

type word = char list

(* type regexpr =
  | Failure
  | Epsilon
  | Character of char
  | Disjunction of regexpr * regexpr
  | Sequence of regexpr * regexpr
  | Repetition of regexpr *)


(** Converts the [regex] type to the [re] type defined in [regex.ml]
    - This function was manually written *)  
(* let rec re_of_regex (regex : regexpr) : re = 
  match regex with 
  | Failure -> Void 
  | Epsilon -> Epsilon 
  | Character c -> Char c 
  | Sequence (r1, r2) -> Seq (re_of_regex r1, re_of_regex r2)
  | Disjunction (r1, r2) -> Alt (re_of_regex r1, re_of_regex r2)
  | Repetition r -> Star (re_of_regex r) *)
  
(** Converts the [re] type defined in [regex.ml] to the [regex] type above
    - This function was manually written *)    
(* let rec regex_of_re (re : re) : regexpr = 
  match re with 
  | Void -> Failure 
  | Epsilon -> Epsilon 
  | Char c -> Character c 
  | Seq (r1, r2) -> Sequence (regex_of_re r1, regex_of_re r2)
  | Alt (r1, r2) -> Disjunction (regex_of_re r1, regex_of_re r2)
  | Star r -> Repetition (regex_of_re r) *)

(** val nullable : regexpr -> bool *)
let rec nullable = function
| Void -> false
| Char _ -> false
| Alt (l, r) -> if nullable l then true else nullable r
| Seq (l, r) -> if nullable l then nullable r else false
| _ -> true

type context = re list

(** [zipper = (regexpr list) set] *)
type zipper = context set

let zipper_union : zipper -> zipper -> zipper = ListSet.union 

let focus (e : re) : zipper = [[e]]

(** val derive_down : char -> regexpr -> context -> zipper *)
let rec derive_down (c : char) (e : re) (ctx : context) : zipper =
  match e with
  | Char cl -> if Char.equal cl c then ctx::[] else []
  | Alt (l, r) ->
    zipper_union (derive_down c l ctx) (derive_down c r ctx)
  | Seq (l, r) ->
    if nullable l
    then zipper_union (derive_down c l (r::ctx)) (derive_down c r ctx)
    else derive_down c l (r::ctx)
  | Star e' -> derive_down c e' (e::ctx)
  | _ -> []

(** val derive_up : char -> context -> zipper *)
let rec derive_up (c : char) (ctx : context) : zipper = 
  match ctx with
  | [] -> []
  | e::ctx' ->
    if nullable e
    then zipper_union (derive_down c e ctx') (derive_up c ctx')
    else derive_down c e ctx'


let derive (c : char) (z : zipper) : zipper =
  List.fold_left zipper_union [] (List.map (derive_up c) z)

let rec derive_word (w : char list) (z : zipper) : zipper =
  match w with
  | [] -> z
  | c::w' -> derive_word w' (derive c z)

let zipper_nullable (z : zipper) : bool =
  List.exists (fun ctx -> List.for_all nullable ctx) z

let zipper_accepts (z : zipper) (w : char list) : bool =
  zipper_nullable (derive_word w z)

let accepts (e : re) (w : char list) : bool =
  zipper_accepts (focus e) w

(** Determines whether a string matches a regex using zippers *)
let zipper_match (r : re) (s : string) : bool = 
  accepts r (Base.String.to_list s)

(******************************************************************************)
let flatten_zipper (z : zipper) : re = 
  List.fold_left (fun acc ctx -> alt acc (List.fold_left (fun acc' r -> seq acc' r) Epsilon ctx)) 
    Void z


