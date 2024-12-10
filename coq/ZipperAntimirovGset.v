Require Export List ListSet Ascii Bool.
Import ListNotations.
Require Export Regex Height.
Require Import Regex EdelmannGset Antimirov RegexOpt.
From stdpp Require Import gmap sets fin_sets.

(* Work in progress: proving that the underlying sets 
   for zippers & Antimirov derivatives are equivalent *)
(******************************************************************************)

(* Maps a function over a zipper, returning a set of regexes *)
Definition zipper_map (f : context -> re) (z : zipper) : gset re :=
  set_map f z.

(* Converts a [context] (used in Edelmann's zipper representation) to a regex 
   by folding the [concat] smart constructor over the context *)
Definition context_to_re (ctx : context) : re :=
  List.fold_left RegexOpt.concat ctx Epsilon.

Lemma empty_context_is_epsilon : 
  context_to_re [] = Epsilon.
Proof.
  unfold context_to_re. simpl. reflexivity.
Qed.      

(* TODO: convert the rest of [ZipperAntimirov.v] from [ListSet] to [gset] *)

