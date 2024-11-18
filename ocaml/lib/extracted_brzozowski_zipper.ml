
(** Finite sets implemented using lists *)
module ListSet = struct
  type 'a t = 'a list

  let empty = []
  let is_empty lst = lst == []
  let mem x lst = List.mem x lst
  let add x s = if mem x s then s else x :: s
  let rem x = List.filter (( <> ) x)
  let dedup lst = lst |> List.sort_uniq Stdlib.compare
  let size s = s |> dedup |> List.length
  let union s1 s2 = s1 @ s2 |> dedup
  let intersect lst1 lst2 = List.filter (fun h -> mem h lst2) lst1
end

(******************************************************************************)
(* Code below is extracted from the Coq code in [Edelmann.v] 
   (lightly modified to use the functions from the [ListSet] module above) *)

type 'a set = 'a list

type word = char list

type regexpr =
| Failure
| Epsilon
| Character of char
| Disjunction of regexpr * regexpr
| Sequence of regexpr * regexpr
| Repetition of regexpr

(** val nullable : regexpr -> bool **)

let rec nullable = function
| Failure -> false
| Character _ -> false
| Disjunction (l, r) -> if nullable l then true else nullable r
| Sequence (l, r) -> if nullable l then nullable r else false
| _ -> true

type context = regexpr list


type zipper = context set

(** val zipper_union : context set -> context set -> context set **)

let zipper_union = ListSet.union 

(** val focus : regexpr -> zipper **)

let focus e =
  (e::[])::[]

(** val derive_down : char -> regexpr -> context -> zipper **)

let rec derive_down c e ctx =
  match e with
  | Character cl -> if Char.equal cl c then ctx::[] else []
  | Disjunction (l, r) ->
    zipper_union (derive_down c l ctx) (derive_down c r ctx)
  | Sequence (l, r) ->
    if nullable l
    then zipper_union (derive_down c l (r::ctx)) (derive_down c r ctx)
    else derive_down c l (r::ctx)
  | Repetition e' -> derive_down c e' (e::ctx)
  | _ -> []

(** val derive_up : char -> context -> zipper **)

let rec derive_up c = function
| [] -> []
| e::ctx' ->
  if nullable e
  then zipper_union (derive_down c e ctx') (derive_up c ctx')
  else derive_down c e ctx'

(** val derive : char -> zipper -> zipper **)

let derive c z =
  List.fold_left zipper_union [] (List.map (derive_up c) z)

(** val derive_word : char list -> zipper -> zipper **)

let rec derive_word w z =
  match w with
  | [] -> z
  | c::w' -> derive_word w' (derive c z)

(** val zipper_nullable : regexpr list list -> bool **)

let zipper_nullable z =
  List.exists (fun ctx -> List.for_all nullable ctx) z

(** val zipper_accepts : zipper -> word -> bool **)

let zipper_accepts z w =
  zipper_nullable (derive_word w z)

(** val accepts : regexpr -> char list -> bool **)

let accepts e w =
  zipper_accepts (focus e) w
