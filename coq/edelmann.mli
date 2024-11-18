
type sumbool =
| Left
| Right

val eqb : bool -> bool -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type 'a set = 'a list

val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type word = char list

type regexpr =
| Failure
| Epsilon
| Character of char
| Disjunction of regexpr * regexpr
| Sequence of regexpr * regexpr
| Repetition of regexpr

val nullable : regexpr -> bool

type context = regexpr list

val context_eq_dec : context -> context -> sumbool

type zipper = context set

val zipper_union : context set -> context set -> context set

val focus : regexpr -> zipper

val derive_down : char -> regexpr -> context -> zipper

val derive_up : char -> context -> zipper

val derive : char -> zipper -> zipper

val derive_word : char list -> zipper -> zipper

val zipper_nullable : regexpr list list -> bool

val zipper_accepts : zipper -> word -> bool

val accepts : regexpr -> char list -> bool
