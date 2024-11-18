
type sumbool =
| Left
| Right

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> if f a then true else existsb f l0

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> if f a then forallb f l0 else false

type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a::[]
| a1::x1 ->
  (match aeq_dec a a1 with
   | Left -> a1::x1
   | Right -> a1::(set_add aeq_dec a x1))

(** val set_union :
    ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
| [] -> x
| a1::y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  if if if if if if if eqb a0 b0 then eqb a1 b1 else false
                 then eqb a2 b2
                 else false
              then eqb a3 b3
              else false
           then eqb a4 b4
           else false
        then eqb a5 b5
        else false
     then eqb a6 b6
     else false
  then eqb a7 b7
  else false

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

(** val context_eq_dec : context -> context -> sumbool **)

let rec context_eq_dec l x =
  match l with
  | [] -> (match x with
           | [] -> Left
           | _::_ -> Right)
  | y::l0 ->
    (match x with
     | [] -> Right
     | r::l1 ->
       (match let rec f r0 x0 =
                match r0 with
                | Failure -> (match x0 with
                              | Failure -> Left
                              | _ -> Right)
                | Epsilon -> (match x0 with
                              | Epsilon -> Left
                              | _ -> Right)
                | Character c ->
                  (match x0 with
                   | Character c0 ->
                     let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = c in
                     let Ascii (b7, b8, b9, b10, b11, b12, b13, b14) = c0 in
                     if b
                     then if b7
                          then if b0
                               then if b8
                                    then if b1
                                         then if b9
                                              then if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                              else Right
                                         else if b9
                                              then Right
                                              else if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                    else Right
                               else if b8
                                    then Right
                                    else if b1
                                         then if b9
                                              then if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                              else Right
                                         else if b9
                                              then Right
                                              else if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                          else Right
                     else if b7
                          then Right
                          else if b0
                               then if b8
                                    then if b1
                                         then if b9
                                              then if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                              else Right
                                         else if b9
                                              then Right
                                              else if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                    else Right
                               else if b8
                                    then Right
                                    else if b1
                                         then if b9
                                              then if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                              else Right
                                         else if b9
                                              then Right
                                              else if b2
                                                   then if b10
                                                        then if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                        else Right
                                                   else if b10
                                                        then Right
                                                        else if b3
                                                             then if b11
                                                                  then 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                  else Right
                                                             else if b11
                                                                  then Right
                                                                  else 
                                                                    if b4
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b12
                                                                    then Right
                                                                    else 
                                                                    if b5
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                                                                    else Right
                                                                    else 
                                                                    if b13
                                                                    then Right
                                                                    else 
                                                                    if b6
                                                                    then 
                                                                    if b14
                                                                    then Left
                                                                    else Right
                                                                    else 
                                                                    if b14
                                                                    then Right
                                                                    else Left
                   | _ -> Right)
                | Disjunction (l2, r1) ->
                  (match x0 with
                   | Disjunction (l3, r2) ->
                     (match f l2 l3 with
                      | Left -> f r1 r2
                      | Right -> Right)
                   | _ -> Right)
                | Sequence (l2, r1) ->
                  (match x0 with
                   | Sequence (l3, r2) ->
                     (match f l2 l3 with
                      | Left -> f r1 r2
                      | Right -> Right)
                   | _ -> Right)
                | Repetition e ->
                  (match x0 with
                   | Repetition e0 -> f e e0
                   | _ -> Right)
              in f y r with
        | Left -> context_eq_dec l0 l1
        | Right -> Right))

type zipper = context set

(** val zipper_union : context set -> context set -> context set **)

let zipper_union =
  set_union context_eq_dec

(** val focus : regexpr -> zipper **)

let focus e =
  (e::[])::[]

(** val derive_down : char -> regexpr -> context -> zipper **)

let rec derive_down c e ctx =
  match e with
  | Character cl -> if eqb0 cl c then ctx::[] else []
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
  fold_right zipper_union [] (map (derive_up c) z)

(** val derive_word : char list -> zipper -> zipper **)

let rec derive_word w z =
  match w with
  | [] -> z
  | c::w' -> derive_word w' (derive c z)

(** val zipper_nullable : regexpr list list -> bool **)

let zipper_nullable z =
  existsb (fun ctx -> forallb nullable ctx) z

(** val zipper_accepts : zipper -> word -> bool **)

let zipper_accepts z w =
  zipper_nullable (derive_word w z)

(** val accepts : regexpr -> char list -> bool **)

let accepts e w =
  zipper_accepts (focus e) w
