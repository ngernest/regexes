Require Export List ListSet Ascii Bool.
Import ListNotations.
Require Export Regex Height.
Require Import Regex Edelmann Antimirov RegexOpt.
From stdpp Require Import gmap sets fin_sets.

(* Work in progress: proving that the underlying sets 
   for zippers & Antimirov derivatives are equivalent *)
(******************************************************************************)

(* Maps a function over a zipper, returning a set of regexes *)
Definition zipper_map (f : context -> re) (z : zipper) : ListSet.set re :=
  ListSet.set_map re_eq_dec f z.

(* Converts a [context] (used in Edelmann's zipper representation) to a regex 
   by folding the [concat] smart constructor over the context *)
Definition context_to_re (ctx : context) : re :=
  List.fold_left RegexOpt.concat ctx Epsilon.

(* The underlying regex set that forms the zipper representation of 
   Brozozwski derivatives (from Edelmann's dissertation) *)
Definition underlying_zipper_set (r : re) (c : char) : gset re :=
  list_to_set ((zipper_map context_to_re (derive c (focus r))) : list re).
  
(* The underlying regex set formed after taking the Antimirov derivative *)
Definition underlying_antimirov_set (r : re) (c : char) : gset re :=
  a_der r c.

(* The zipper of a union is the union of two zippers *)
Lemma zipper_union_homomorphism : forall (r1 r2 : re) (c : char),
  underlying_zipper_set (Regex.Union r1 r2) c = 
  underlying_zipper_set r1 c ∪ underlying_zipper_set r2 c.
Proof.  
  intros.
  unfold underlying_zipper_set. 
  induction r2; unfold derive, focus; 
    simpl; eauto.
  - (* Void *)
    destruct (Edelmann.nullable r1); simpl; set_solver.
  - (* Epsilon *) 
    destruct (Edelmann.nullable r1); simpl; set_solver.
  - (* Atom *)
    destruct (Edelmann.nullable r1); simpl.
    destruct ((c0 =? c)%char) eqn:E.
    + (* c = c0 *)
      simpl. 
      (* TODO: figure out how to continue this *)
Admitted.       
    
(* The underlying sets for zippers & Antimirov derivatives are equivalent *)
Lemma zipper_antimirov_equivalent : forall (r : re) (c : char),
  underlying_zipper_set r c = underlying_antimirov_set r c.
Proof.
  intros. induction r.
  - (* Void *)
    unfold underlying_zipper_set. simpl. auto.
  - (* Epsilon *) 
    unfold underlying_zipper_set. simpl. auto.
  - (* Atom *)
     unfold underlying_zipper_set. simpl. auto.
     destruct (char_dec c c0).
     + (* c = c0 *) 
       unfold focus, derive. simpl. 
       assert ((c =? c0)%char = true).
      { rewrite <- reflect_iff. apply e.
         apply Ascii.eqb_spec. }
       rewrite <- Ascii.eqb_sym.
       rewrite H. simpl. 
       unfold context_to_re. 
       simpl. set_solver.
     + (* c <> c0 *)
       simpl. unfold context_to_re.
       unfold focus, derive. simpl.
       assert ((c =? c0)%char = false).
       { rewrite Ascii.eqb_neq. assumption. }
       rewrite Ascii.eqb_sym. 
       rewrite H. simpl. auto.
  - (* Union *)
    simpl. rewrite zipper_union_homomorphism.
    set_solver.
  - (* Concat *)
Admitted. (* TODO *)  

