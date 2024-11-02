open Base

(* -------------------------------------------------------------------------- *)
(*                               1.1 Background                               *)
(* -------------------------------------------------------------------------- *)

(* The stuff in this section is largely the same as [harper.ml], 
  modulo some renaming *)

(** A datatype for regular expressions *)
type re = 
  | Void 
  | Eps 
  | Char of char 
  | Seq of re * re 
  | Alt of re * re 
  | Star of re
[@@deriving sexp]  

(** [omatch] matches some initial segment of [cs] against the regex [r],
    and pases the corresponding final segment to the continuation [k] *)
let rec omatch (r : re) (k : char list -> bool) (cs : char list) : bool =
  match (r, cs) with
  | Void, _ -> false
  | Eps, _ -> k cs
  | Char _, [] -> false
  | Char c, c' :: cs -> if Char.equal c c' then k cs else false
  | Alt (r1, r2), _ -> omatch r1 k cs || omatch r2 k cs
  | Seq (r1, r2), _ -> omatch r1 (fun s' -> omatch r2 k s') cs
  | Star r0, _ -> k cs || omatch r0 (fun s' -> omatch r k s') cs

(** Determines whether a string matches a regex *)
let omatchtop (r : re) (cs : char list) : bool = 
  omatch r List.is_empty cs

(* Problem: this matcher can loop forever when the [r0] in [Star r0] is 
  {i nullable} (i.e. it accepts the empty string).

   We want a frugal way of detecting / preventing loops! 
   This is addressed in the next section. *)

(* -------------------------------------------------------------------------- *)
(*                          2.1 Ensuring termination                          *)
(* -------------------------------------------------------------------------- *)

(* --------------------- A termination-augmented matcher -------------------- *)

(** Same as [omatch], but with an extra argument [b], which tracks whether 
    the character has been consumed since the start of the current iteration. 
    Intuition: 
    - [b] is set to true after a successful [Char c] match 
    - [b] is cleared before matching the body [r0] of an iteration [Star r0] 
    - [b] is passed along unchanged for all other cases *)
let rec re_match (r : re) (k : bool -> char list -> bool) 
  (b : bool) (cs : char list) : bool =
  match (r, cs) with
  | Void, _ -> false
  | Eps, _ -> k b cs
  | Char _, [] -> false
  | Char c, c' :: s' -> Char.equal c c' && k true s'
  | Alt (r1, r2), _ -> re_match r1 k b cs || re_match r2 k b cs
  | Seq (r1, r2), _ -> re_match r1 (fun b' s' -> re_match r2 k b' s') b cs
  | Star r0, _ ->
    (* [k'] is a single-use continuation, used only in the [Star] case 
      (Filinski says the purpose of [k'] is to satsify some syntactic 
      property later on in the paper) *)
    let k' (bf : bool) (ss : char list) : bool =
      re_match r0 (fun b' s' -> b' && re_match (Star r0) k b' s') bf ss in
    k b cs || k' false cs

(** Determines whether a string matches a regex *)
let re_matchtop (r : re) (cs : char list) : bool =
  re_match r (fun _ xs -> List.is_empty xs) true cs

(* ------------ A defunctionalized termination-augmented matcher ------------ *)

(** Datatype for defunctionalized continuations: 
    these keep track of the free variables in the body of the continuation *)
type cont =
  | CInit
  (* [CThen (r, k)] corresponds to [fun b s -> match r k b s] *)
  | CThen of re * cont
  (* [CStar (r, k)] represents [CThen (Star r, k)], but also checks whether 
     the guard [b] is true, i.e. [fun b s -> b && match r k b s] *)
  | CStar of re * cont

let rec fmatch (r : re) (k : cont) (b : bool) (s : char list) : bool =
  match (r, s) with
  | Char _, [] -> false
  | Char c, c' :: s' -> Char.equal c c' && apply k true s'
  | Eps, _ -> apply k b s
  | Seq (r1, r2), _ -> fmatch r1 (CThen (r2, k)) b s
  | Void, _ -> false
  | Alt (r1, r2), _ -> fmatch r1 k b s || fmatch r2 k b s
  | Star r0, _ -> apply k b s || apply (CThen (r0, CStar (r0, k))) false s

(** Builds up the body of the continuation *)
and apply (k : cont) (b : bool) (s : char list) : bool =
  match (k, s) with
  | CInit, _ -> false
  | CThen (r, k), _ -> fmatch r k b s
  | CStar (r, k), _ -> b && fmatch (Star r) k b s

(** Top-level regex matcher *)
let fmatchtop (r : re) (s : char list) : bool = fmatch r CInit true s

(* -------------------------------------------------------------------------- *)
(*                   3: Specializing the matcher to a regex                   *)
(* -------------------------------------------------------------------------- *)

(* To improve efficiency, we {i stage} the matching process by compiling the 
   regex to abstract machine code and pass the code label 
   (the {i continuation number}) around.
   Instead of applying the continuation, we just generate code for a call *)

(** [contno] represents {i continuation numbers}, i.e. the code label *)
type contno = CN of int
[@@deriving sexp]

(** [comp] is the type of possible continuation bodies:   
    - [AtEnd]: the computation that succeeds iff there are no chars 
      left in the string 
    - [Expect (c, i)]: checks that the first char (if any) of the string is [c],
      and invokes continuation [i] on the remainder of the string, 
      with the flag set to true. If the first char isn't [c], 
      the computation fails. 
    - [Cont (p, i)]: invokes continuation [i] on the current string. 
      If [p] is false, the flag bit is set to false, 
      otherwise it is passed along unmodified. 
    - [Fail]: always fails 
    - [Or (f1, f2)]: succeeds if at least one of [f1] & [f2] succeeds, 
      fails otherwise *)
type comp =
  | AtEnd
  | Expect of char * contno
  | Cont of bool * contno
  | Fail
  | Or of comp * comp
[@@deriving sexp]  

(** [ccomp] is a pair consisting of a [bool] and a [comp]utation. 
    The bool specifies whether the computation is [unconditional]: 
    - unconditional computations are always evaluated
    - conditional computations are only evaluated if the character-consumption 
      flag is currently true, and fails immediately otherwise *)
type ccomp = bool * comp
[@@deriving sexp]

(** [pgm] is the type of {i programs}. A program is consists of a [ccomp] 
    for each continuation position *)
type pgm = ccomp list * contno
[@@deriving sexp]

(** [trans] takes as arguments:
    - a regex [r]
    - the continuation number [i] to be invoked on success
    - an allocation counter [n] (the first unused continuation number)

    [trans] returns a triple consisting of:
    - the computation [f] representing the regex 
    - a (possibly empty) list [gs] of generated continuation definitions 
    - the updated allocation counter [n'], where [n' = n + |gs| ] *)
let rec trans (r : re) (i : contno) (n : int) : comp * ccomp list * int =
  match r with
  | Char c -> (Expect (c, i), [], n)
  | Eps -> (Cont (true, i), [], n)
  | Seq (r1, r2) ->
    let f2, gs2, n2 = trans r2 i n in
    let f1, gs1, n1 = trans r1 (CN n2) (n2 + 1) in
    (f1, gs2 @ [ (true, f2) ] @ gs1, n1)
  | Void -> (Fail, [], n)
  | Alt (r1, r2) ->
    let f1, gs1, n1 = trans r1 i n in
    let f2, gs2, n2 = trans r2 i n1 in
    (Or (f1, f2), gs1 @ gs2, n2)
  | Star r0 ->
    let f0, gs0, n0 = trans r0 (CN n) (n + 1) in
    let f1 = Or (Cont (true, i), Cont (false, CN n0)) in
    (f1, [ (false, f1) ] @ gs0 @ [ (true, f0) ], n0 + 1)

(** [transtop] compiles a regex to a program: 
    it defines continuation number 0 to be the {i initial continuation} 
    (i.e. the one that checks that nothing is left), 
    and also generates an explicit definition for the main continuation 
    so that it can be referenced by a number. *)
let transtop (r : re) : pgm =
  let f, gs, n = trans r (CN 0) 1 in
  ([ (true, AtEnd) ] @ gs @ [ (true, f) ], CN n)


(* -------------------------------------------------------------------------- *)
(*                         A backtracking interpreter                         *)
(* -------------------------------------------------------------------------- *)

(** Interprets a list of instructions [gs], a continuation [comp], 
    the flag [b] and matches the compiled regex against the string [s] *)
let rec interp (gs : ccomp list) (comp : comp) 
  (b : bool) (s : char list) : bool =
  match (comp, s) with
  | AtEnd, [] -> true
  | AtEnd, _ -> false
  | Expect (_, _), [] -> false
  | Expect (c, i), c' :: s' -> Char.equal c c' && interpi gs i true s'
  | Cont (true, i), _ -> interpi gs i b s
  | Cont (false, i), _ -> interpi gs i false s
  | Fail, _ -> false
  | Or (f1, f2), _ -> interp gs f1 b s || interp gs f2 b s

and interpc (gs : ccomp list) (ccomp : ccomp) 
  (b : bool) (s : char list) : bool =
  match ccomp with
  | true, f -> interp gs f b s
  | false, f -> b && interp gs f b s

and interpi (gs : ccomp list) (CN n : contno) (b : bool) 
  (s : char list) : bool =
  interpc gs (List.nth_exn gs n) b s

(** Runs the result of compiling a regex to a staged computation *)
let irun ((gs, i1) : ccomp list * contno) (s : char list) : bool = 
  interpi gs i1 true s

(** Top-level regex matcher *)
let imatchtop (r : re) (s : string) : bool = 
  let pgm = transtop r in 
  Stdio.printf "Compiled program:\n";
  Stdio.printf "%s\n" (Sexp.to_string_hum (sexp_of_pgm pgm));
  irun (transtop r) (String.to_list s)
