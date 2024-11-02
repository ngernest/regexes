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
  | Alt(r, r') -> R.union (aderiv c r) (aderiv c r')
  | Seq(r1, r2) -> R.union (rmap (fun r1' -> Seq(r1', r2)) (aderiv c r1))
                           (if null r1 then aderiv c r2 else R.empty)
  | Star r -> rmap (fun r' -> Seq(r', Star r)) (aderiv c r)

(** Applies the Antimirov derivative to a whole set of regexes, 
    and takes the union *)
let deriv (c : char) (rs : R.t) : R.t = 
  R.fold (fun r acc -> R.union (aderiv c r) acc) rs R.empty

(** A datatype for DFAs *)
type dfa = {
  size : int; 
  fail : int; 
  trans : (int * char * int) list; 
  final : int list
}

let rec enum f v i max = if i < max then enum f (f i v) (i+1) max else v
let charfold f init  = enum (fun i -> f (Char.chr i)) init 0 256
    
let dfa r =
  let find rs (n,m) = try M.find rs m, (n,m) with _ -> n, (n+1, M.add rs n m) in
  let rec loop s v t f rs =
    let (x, s) = find rs s in
    if I.mem x v then (s, v, t, f)
    else charfold (fun c (s, v, t, f) ->
                     let rs' = deriv c rs in
                     let (y, s) = find rs' s in
                     loop s v ((x,c,y) :: t) f rs')
           (s, I.add x v, t, if R.exists null rs then x :: f else f) in
  let (s, v, t, f) = loop (0, M.empty) I.empty [] [] (R.singleton r) in
  let (fail, (n, m)) = find R.empty s in 
  { size = n; fail = fail; trans= t; final = f }
      
type table = { m : int array array; accept : bool array; error : int }

let table d = 
  { error = d.fail;
    accept = Array.init d.size (fun i -> List.mem i d.final);
    m = (let a = Array.init d.size (fun _ -> Array.make 256 0) in
         List.iter (fun (x, c, y) -> a.(x).(Char.code c) <- y) d.trans; a) }

let rec matches' t s i x =
  if i < String.length s && x != t.error 
  then matches' t s (i+1) t.m.(x).(Char.code s.[i])
  else t.accept.(x)

let re_match t s = matches' t s 0 0

let charset s = enum (fun i r -> Alt(C s.[i], r)) Bot 0 (String.length s)
let string s = enum (fun i r -> Seq(r, C s.[i])) Nil 0 (String.length s)
let seq rs = List.fold_right (fun r rs -> Seq(r, rs)) rs Nil
let alt rs = List.fold_right (fun r rs -> Alt(r, rs)) rs Bot
let opt r = Alt(r, Nil)
let star r = Star r
let plus r = Seq(r, star r)

let print_table out t =
  Array.iteri (fun x row ->
    Array.iteri (fun c y ->
      if x != t.error && y != t.error then
        (Format.fprintf out "%d '%c' --> %d " x (Char.chr c) y;
         (if t.accept.(y) then Format.fprintf out "*");
         Format.fprintf out "\n"))
      row)
    t.m
   
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
