
Require Export List Ascii Bool.
Require Import Regex RegexOpt.
Import ListNotations.
From stdpp Require Import gmap sets fin_sets.

(* Variant of Edelmann.v, adapted to work with [gset]s instead of [ListSet] *)

(***** CHARACTERS AND WORDS *****)

Global Declare Scope char_class_scope.
Open Scope char_class_scope.

(* Input characters. *)
Definition char := ascii.
Definition char_dec := ascii_dec.

(* Input words. *)
Definition word := list char.


(***** CONTEXTS AND ZIPPERS *****)

(* Contexts are sequences of regular expressions. *)
Definition context := list re.

(* Zippers are disjunctions of contexts. *)
Definition zipper := gset context.

(* Union of two zippers. *)
Definition zipper_union (z1 : zipper) (z2 : zipper) : zipper := z1 ∪ z2.

(* Addition of a context in a zipper. *)
Definition zipper_add (ctx : context) (z : zipper) : zipper := 
  z ∪ {[ ctx ]}.

(* Convert a regular expression into a zipper. *)
Definition focus (e: re) : zipper := singleton [e].

(* Typeclass instance needed to make the definition of [unfocus] below 
   typecheck *)
Instance ContextElements : Elements re context := {
  elements := fun ctx => ctx
}.

(* Conversion from zipper back to re. 
 * Unused, but provides some intuition on zippers.
 *)
Definition unfocus (z : zipper) : re :=
  let ds := set_map (fun ctx => set_fold RegexOpt.concat Epsilon ctx) z in
  set_fold Regex.Union Void (ds : gset re).

(***** DERIVATION *****)

(* Downwards phase of Brzozowski's derivation on zippers. *)
Fixpoint derive_down (c : char) (e : re) (ctx : context) : zipper :=
  match e with
  | Atom cl => if Ascii.eqb cl c then {[ ctx ]} else ∅ 
  | Regex.Union l r => zipper_union (derive_down c l ctx) (derive_down c r ctx)
  | Concat l r => 
    if (isEmpty l) then
      zipper_union (derive_down c l (r :: ctx)) (derive_down c r ctx)
    else
      derive_down c l (r :: ctx)
  | Star e' => derive_down c e' (e :: ctx) 
  | _ => ∅ 
  end.

(* Upwards phase of Brzozowski's derivation on zippers. *)
Fixpoint derive_up (c : char) (ctx : context) : zipper :=
  match ctx with
  | [] => ∅ 
  | e :: ctx' => if isEmpty e
    then 
      zipper_union (derive_down c e ctx') (derive_up c ctx')
    else
      derive_down c e ctx'
  end.


(* Some typeclass instances needed to make the definition of [derive]
   below typecheck *)
Instance ZipperElements : Elements zipper zipper := {
  elements := fun z => [z]
}. 

Instance ZipperSingleton : Singleton zipper zipper := {
  singleton := fun z => z
}.

(* Brzozowski derivatives for zippers *)
Definition derive (c : char) (z : zipper) : zipper :=
  set_fold zipper_union ∅  
    (set_map (derive_up c) z : zipper).

(* Generalisation of derivatives to words. *)
Fixpoint derive_word (w : word) (z : zipper) : zipper :=
  match w with
  | [] => z
  | c :: w' => derive_word w' (derive c z)
  end.

(* Note: the following 3 functions return [Prop] instead of [bool], 
   as is the case for their implementations in [Edelmann.v].
   This is because there does not exist a version of [existsb] for [gset]s 
   ([existsb] comes from [ListSet] only).
   
   TODO: can we pattern match on [gset]s and implement our own version of 
   [existsb] for [gset bool]? *)  

(* Checks if the zipper z accept the empty word *)
Definition zipper_nullable (z : zipper) : Prop :=
  set_Exists (fun ctx => forallb isEmpty ctx) z.

(* Checks if zipper [z] accepts the word [w] *)
Definition zipper_accepts (z : zipper) (w : word) : Prop :=
  zipper_nullable (derive_word w z).  

(* Checks if the word [w] matches the regular expression [e] *)
Definition accepts (e : re) (w : list char) : Prop :=
  zipper_accepts (focus e) w.  

