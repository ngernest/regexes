(* A regex matcher based on Antimirov derivatives, 
   code from Neel Krishnaswami 
   
   https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html
*)

type re = 
  | C of char 
  | Nil 
  | Seq of re * re 
  | Bot 
  | Alt of re * re 
  | Star of re

(** Checks if a regex accepts the empty string *)
let rec null (r : re) : bool = 
  match r with 
  | C _ | Bot -> false
  | Nil | Star _ -> true
  | Alt(r1, r2) -> null r1 || null r2
  | Seq(r1, r2) -> null r1 && null r2

(** [R] is the type of finite sets of regexes *)  
module R = Set.Make(struct 
  type t = re 
  let compare = compare 
end)

(** [rmap] maps a function over a set of regexes, building a new regex *)
let rmap (f : re -> re) (rs : R.t) : R.t = 
  R.fold (fun r -> R.add (f r)) rs R.empty

(** [M] is the type of finite maps where the keys are sets of regexes *)
module M = Map.Make(R)

(** [I] is the type of sets of [int]s *)
module I = Set.Make(struct 
  type t = int 
  let compare = compare 
end)

(** [aderiv c r] is the Antimirov derivative of the regex [r] with respect 
    to the character [c]. This returns a set of partial derivatives, which 
    collectively accept the same strings as the Brzozowski derivative. *)
let rec aderiv (c : char) (r : re) : R.t = 
  match r with
  | C c' when c = c' -> R.singleton Nil 
  | C _ | Nil | Bot -> R.empty
  | Alt (r, r') -> R.union (aderiv c r) (aderiv c r')
  | Seq (r1, r2) -> R.union (rmap (fun r1' -> Seq(r1', r2)) (aderiv c r1))
                           (if null r1 then aderiv c r2 else R.empty)
  | Star r -> rmap (fun r' -> Seq(r', Star r)) (aderiv c r)

(** Applies the Antimirov derivative to a whole set of regexes, 
    and takes the union *)
let deriv (c : char) (rs : R.t) : R.t = 
  R.fold (fun r acc -> R.union (aderiv c r) acc) rs R.empty

(* Since the set of partial derivatives is finite, 
  this means that the powerset of this set is also finite, 
   and so by treating sets of partial derivatives as states,
   we can construct a DFA for matching regexes *)

(** A datatype for DFAs:
    - [size] is the no. of states 
      (we index states using [int]s from [0] to [size - 1]) 
    - [fail] is the sink state for non-matching strings
    - [trans] is a list of transitions 
    - [final] is a list of accepting states *)
type dfa = {
  size : int; 
  fail : int; 
  trans : (int * char * int) list; 
  final : int list
}

(** [enum] is a for-loop ranging from [i] to [max] *)
let rec enum (f : int -> 'a -> 'a) (v : 'a) (i : int) (max : int) : 'a = 
  if i < max 
    then enum f (f i v) (i + 1) max 
  else v

(** Folds a function [f] over all of the ASCII characters *)
let charfold (f : char -> 'a -> 'a) (init : 'a) : 'a = 
  enum (fun i -> f (Char.chr i)) init 0 256

(** Constructs a DFA from a regex *)
let dfa (r : re) : dfa =
  (** Takes a set [rs] of regexes and returns a numeric index for it. 
     - It uses a state [(n, m)], where [n] is a counter for generating 
       fresh variables, and [m] is a map which maps sets of regexes 
       to their indices *)
  let find (rs : R.t) ((n, m) : int * int M.t) : int * (int * int M.t) = 
    try M.find rs m, (n, m) with 
    _ -> n, (n + 1, M.add rs n m) in
  (** [loop] is where the main work happens: 
      - [s] is the state parameter for [find]
      - [v] is the set of states ([int]s) we've visited so far
      - [t] is the list of transitions we've built so far 
      - [f] is the final states we've generated so far 
      - [rs] is the current working set of regexes *)
  let rec loop (s : int * int M.t) (v : I.t) (t : (int * char * int) list) 
    (f : int list) (rs : R.t) =
    let (x, s) = find rs s in
    if I.mem x v then (s, v, t, f)
    else charfold (fun c (s, v, t, f) ->
                     let rs' = deriv c rs in
                     let (y, s) = find rs' s in
                     loop s v ((x,c,y) :: t) f rs')
           (s, I.add x v, t, if R.exists null rs then x :: f else f) in
  let (s, v, t, f) = loop (0, M.empty) I.empty [] [] (R.singleton r) in
  let (fail, (n, m)) = find R.empty s in 
  { size = n; 
    fail = fail; 
    trans = t; 
    final = f }

(** A datatype for regex matching tables:
    - [m] is the transition table 
    - [accept] is an array of [bool]s indicating 
      if the state is an accepting state 
    - [error] is the index of the error state *)    
type table = { 
  m : int array array; 
  accept : bool array; 
  error : int 
}

(** Builds a table-based matcher from a [dfa] (it builds a nested array of [int]s
    and initializes it using the list of transitions) *)
let table (d : dfa) : table = 
  { error = d.fail;
    accept = Array.init d.size (fun i -> List.mem i d.final);
    m = (let a = Array.init d.size (fun _ -> Array.make 256 0) in
         List.iter (fun (x, c, y) -> a.(x).(Char.code c) <- y) d.trans; a) }

(** [matches'] takes a table [t], a string [s], an index [i] and 
   a current state [x]. It keeps calling itself so long as we haven't consumed
   the entirety of the string or hit the error state, and it reports whether it 
   ends in an accepting state or not.  *)
let rec matches' (t : table) (s : string) (i : int) (x : int) : bool =
  if i < String.length s && x != t.error 
  then matches' t s (i+1) t.m.(x).(Char.code s.[i])
  else t.accept.(x)

(** [re_match] calls [matches'] at index 0, in state 0 *)  
let re_match (t : table) (s : string) : bool = 
  matches' t s 0 0

(* -------------------------------------------------------------------------- *)
(*                   Helper functions for regex constructors                  *)
(* -------------------------------------------------------------------------- *)

(** Constructs a regex that a set of characters in a string *)
let charset (s : string) : re = 
  enum (fun i r -> Alt(C s.[i], r)) Bot 0 (String.length s)

(** Constructs a regex that matches exactly the string [s] *)  
let string (s : string) : re = 
  enum (fun i r -> Seq(r, C s.[i])) Nil 0 (String.length s)

(** Folds [Seq] over a list of regexes *)  
let seq (rs : re list) : re = 
  List.fold_right (fun r rs -> Seq(r, rs)) rs Nil

(** Folds [Alt] over a list of regexes *)
let alt (rs : re list) : re = 
  List.fold_right (fun r rs -> Alt(r, rs)) rs Bot

(** Regex indicating that [r] is optional *)
let opt (r : re) : re = Alt (r, Nil)

(** Kleene star *)
let star (r : re) : re = Star r

(** Matches one or more occurrences of a regex [r] *)
let plus (r : re) : re = Seq (r, star r)

(* -------------------------------------------------------------------------- *)
(*                               Pretty-printing                              *)
(* -------------------------------------------------------------------------- *)

(** Pretty-prints a table [t] using the formatter [out] *)
let print_table (out : Format.formatter) (t : table) : unit =
  Array.iteri (fun x row ->
    Array.iteri (fun c y ->
      if x != t.error && y != t.error then
        (Format.fprintf out "%d '%c' --> %d " x (Char.chr c) y;
         (if t.accept.(y) then Format.fprintf out "*");
         Format.fprintf out "\n"))
      row)
    t.m

(* -------------------------------------------------------------------------- *)
(*                                    Tests                                   *)
(* -------------------------------------------------------------------------- *)
   
module Test = struct
  let digit = charset "0123456789"
  let sign = charset "+-"
  let dot = C '.'
  let dotted = alt [ seq [star digit; dot; plus digit];
                     seq [plus digit; dot; star digit] ]
  let exponent = seq [charset "eE"; opt sign; plus digit]
  let float = alt [seq [opt sign; dotted; opt exponent];
                   seq [opt sign; plus digit; exponent] ]

  let t_float = table (dfa float)
end
