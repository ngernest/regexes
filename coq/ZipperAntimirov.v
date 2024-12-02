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

Lemma empty_context_is_epsilon : 
  context_to_re [] = Epsilon.
Proof.
  unfold context_to_re. simpl. reflexivity.
Qed.      

(* The underlying regex set that forms the zipper representation of 
   Brozozwski derivatives (from Edelmann's dissertation) *)
Definition underlying_zipper_set (r : re) (c : char) : gset re :=
  list_to_set ((zipper_map context_to_re (derive c (focus r))) : list re).
  
(* The underlying regex set formed after taking the Antimirov derivative *)
Definition underlying_antimirov_set (r : re) (c : char) : gset re :=
  a_der r c.

Lemma zipper_map_listset_add_commutes : forall (z : zipper),
  zipper_map context_to_re (ListSet.set_add context_eq_dec [] z) 
    = ListSet.set_add re_eq_dec Epsilon (zipper_map context_to_re z).
Proof.
  intros. induction z as [| x xs IHxs].
  - (* z = [] *)
    simpl. rewrite empty_context_is_epsilon. reflexivity.
  - (* z = x :: xs *)
    simpl. 
    destruct (context_eq_dec [] x).
    simpl.
    + (* x = [] *) 
      subst. 
      repeat (rewrite empty_context_is_epsilon). 
      rewrite <- IHxs.
(* TODO: convert all listsets to gsets? this would require reworking 
   Edelmann's Coq proofs significantly though.

  For this lemma, when z = [], LHS = [Epsilon] but RHS = [Epsilon; Epsilon],
  and these are not equal as ListSets, but if we convert them to gsets,
  they would be equal.
*)      
Admitted.       
      
  
Lemma zipper_union_distributes_over_derive_down: forall (c : char) (r1 r2 : re),
  zipper_map context_to_re
  (zipper_union
    (derive_down c r1 [])
    (derive_down c r2 [])) = 
  ListSet.set_union re_eq_dec
    (zipper_map context_to_re (derive_down c r1 []))
    (zipper_map context_to_re (derive_down c r2 [])).
Proof.
  intros. 
  revert r1. induction r2; simpl; eauto.
  - (* Atom *)
    destruct ((c0 =? c)%char) eqn:E1.
    simpl. rewrite empty_context_is_epsilon.
    induction r1; simpl; eauto.
    + destruct ((c1 =? c)%char) eqn:E2.
      simpl. destruct (context_eq_dec [] []); X.
      simpl. repeat (rewrite empty_context_is_epsilon).
      reflexivity.
    + admit. (* TODO *)
    + destruct (Edelmann.nullable r1_1) eqn:E2.
      admit. (* TODO *)
Admitted. (* TODO *)
  

Lemma derive_down_empty_context_eq : forall (c : char) (r : re),
  list_to_set (zipper_map context_to_re (ListSet.set_add context_eq_dec [] 
    (derive_down c r []))) = 
    list_to_set (zipper_map context_to_re (derive_down c r [])) ∪ 
    ({[ Epsilon ]} : gset re).
Proof.
  intros.
  induction r; simpl; eauto.
  - (* Atom *)
    destruct ((c0 =? c)%char) eqn:E1.
    + (* c0 = c *)
      simpl. destruct (context_eq_dec [] []).
      * simpl. repeat (rewrite empty_context_is_epsilon).
        replace ({[Epsilon]} ∪ ∅ ∪ {[Epsilon]}) with ({[ Epsilon ]} : gset re) 
          by set_solver.
        replace ({[Epsilon]} ∪ ∅) with ({[ Epsilon ]} : gset re) 
          by set_solver.
        reflexivity.
      * unfold not in n. destruct n. reflexivity.
    + (* c0 <> c *)
      simpl. rewrite empty_context_is_epsilon. 
      set_solver.
  - (* Union *) 
     rewrite zipper_union_distributes_over_derive_down.
     admit.     
  - (* Concat *) admit.
  - (* Star *) admit.
Admitted. (* TODO *)
      


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
    + (* c0 = c *)
      simpl.
      rewrite empty_context_is_epsilon. 
      replace ({[ Epsilon ]} ∪ ∅) with ({[ Epsilon ]} : gset re) by set_solver.
      rewrite derive_down_empty_context_eq. reflexivity.
    + (* c0 <> c *)
      simpl. set_solver.
    + destruct ((c0 =? c)%char) eqn:E.
      * (* c0 = c *)
        simpl. rewrite empty_context_is_epsilon.
        replace ({[ Epsilon ]} ∪ ∅) with ({[ Epsilon ]} : gset re) 
          by set_solver.
        rewrite derive_down_empty_context_eq. reflexivity.
      * (* c0 <> c *)
        simpl. set_solver.
  - (* Concat *)
    destruct (Edelmann.nullable r1) eqn:E1; simpl.
    + (* nullable r1 = true *)
      remember (Edelmann.nullable r2_1 || Edelmann.nullable r2_2) as nullable_bool.
      destruct nullable_bool eqn:E2; simpl.
      * (* nullable_bool = true *)
        rewrite zipper_union_distributes_over_derive_down.
        admit. (* TODO *)
      * admit. (* TODO *)
    + admit. (* TODO *)      
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

