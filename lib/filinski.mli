type re =
    Void
  | Eps
  | Char of char
  | Seq of re * re
  | Alt of re * re
  | Star of re
val omatch : re -> (char list -> bool) -> char list -> bool
val omatchtop : re -> char list -> bool
val re_match : re -> (bool -> char list -> bool) -> bool -> char list -> bool
val re_matchtop : re -> char list -> bool
type cont = CInit | CThen of re * cont | CStar of re * cont
val fmatch : re -> cont -> bool -> char list -> bool
val apply : cont -> bool -> char list -> bool
val fmatchtop : re -> char list -> bool
type contno = CN of int
type comp =
    AtEnd
  | Expect of char * contno
  | Cont of bool * contno
  | Fail
  | Or of comp * comp
type ccomp = bool * comp
type pgm = ccomp list * contno
val trans : re -> contno -> int -> comp * ccomp list * int
val transtop : re -> pgm
val interp : ccomp list -> comp -> bool -> char list -> bool
val interpc : ccomp list -> ccomp -> bool -> char list -> bool
val interpi : ccomp list -> contno -> bool -> char list -> bool
val irun : ccomp list * contno -> char list -> bool
val imatchtop : re -> string -> bool
