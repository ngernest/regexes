Require Export List Ascii Bool.
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

(* Empty context corresponds to [Epsilon] *)
Lemma empty_context_is_epsilon : 
  context_to_re [] = Epsilon.
Proof.
  unfold context_to_re. simpl. reflexivity.
Qed.    

(* The underlying regex set that forms the zipper representation of 
   Brozozwski derivatives (from Edelmann's dissertation) *)
Definition underlying_zipper_set (r : re) (c : char) : gset re :=
  zipper_map context_to_re (derive c (focus r)).
  
(* The underlying regex set formed after taking the Antimirov derivative *)
Definition underlying_antimirov_set (r : re) (c : char) : gset re :=
  a_der r c.

(* Typeclass instance needed to make [singleton_empty_ctx_is_singleton_epsilon] 
  below typecheck *)
Instance SingletonReZipper : Singleton re zipper := {
  singleton := fun r => {[ [r] ]}
}.

(* Mapping [context_to_re] over the singleton zipper containing the empty context
  yields the singleton set containing [Epsilon ]*)
Lemma singleton_empty_ctx_is_singleton_epsilon : 
  set_map context_to_re ({[ [] ]} : zipper) = ({[ Epsilon ]} : zipper).
Proof.
  unfold set_map. set_solver.  
Qed.  
  
(* Typeclass instance needed to make [zipper_union_empty_r_L] below typecheck *)
Instance ZipperEmpty : Empty zipper := {
  empty := ∅ 
}.

(* The empty zipper is the right identity for the [zipper_union] operation *)
Lemma zipper_union_empty_r_L : forall (z : zipper),
  zipper_union z ∅ = z.
Proof.
  unfold zipper_union. intros.
  replace (gset_union z ∅) with (z ∪ ∅) by set_solver. 
  set_solver.
Qed.  

Instance SingletonCtxZipper : Singleton context zipper := {
  singleton := fun ctx => {[ ctx ]}
}.

Instance EmptyZipper : Empty zipper := {
  empty := ∅ 
}.

Instance UnionZipper : Union zipper := {
  union := zipper_union
}.

Instance ElementsCtxRe : Elements context re := {
  elements := fun ctx => [[ctx]]
}.

Instance ElementsCtxZipper : Elements context zipper := {
  elements := fun z => elements z
}.

Lemma another : forall x (z : zipper),
  x ∈ z -> x ∈ z ∪ {[[]]}.
Proof.
  Admitted.  


Lemma zipper_union_distributes_over_derive_down: forall (c : char) (r1 r2 : re),
  zipper_map context_to_re
  (zipper_union
    (derive_down c r1 [])
    (derive_down c r2 [])) = 
  (zipper_map context_to_re (derive_down c r1 [])) ∪ 
    (zipper_map context_to_re (derive_down c r2 [])).
Proof.
  intros.
  revert r1.
  induction r2; unfold zipper_map; simpl; eauto; intros r1.
  - (* Void *)
    replace (set_map context_to_re ∅) with (∅ : gset re) by set_solver.
    replace (set_map context_to_re (derive_down c r1 []) ∪ ∅) 
      with (set_map context_to_re (derive_down c r1 []) : gset re) 
      by set_solver.
    unfold zipper_union.
    rewrite zipper_union_empty_r_L.
    reflexivity.
  - (* Epsilon *)
    replace (set_map context_to_re ∅) with (∅ : gset re) by set_solver.
    remember (derive_down c r1 []) as z.
    rewrite zipper_union_empty_r_L.
    set_solver.
  - (* Atom *)
    destruct (c0 =? c)%char eqn:E. 
    + (* c0 = c *)
      set_unfold. intros. split; intros.
      * (* -> *) 
      destruct H as [x0 [H1 H2]].
      left.
      exists x0. split; auto. 
      subst.
      unfold zipper_union in H2.
Admitted.       
      
(* 
      replace (@set_map _ _ ElementsCtxZipper _ _ SingletonReZipper EmptyZipper 
        UnionZipper context_to_re 
        (@singleton context zipper SingletonCtxZipper ([] : context) : zipper)) 
        with ({[ Epsilon ]} : zipper).
       *)
      (* * symmetry. apply singleton_empty_ctx_is_singleton_epsilon. *)


(* TODO: convert the rest of [ZipperAntimirov.v] from [ListSet] to [gset] *)      

(******************************************************************************)

Compute (derive_up "a"%char [Void]).

(* The zipper of a union is the union of two zippers *)
Lemma zipper_union_homomorphism : forall (r1 r2 : re) (c : char),
  underlying_zipper_set (Regex.Union r1 r2) c = 
  underlying_zipper_set r1 c ∪ underlying_zipper_set r2 c.
Proof.
Admitted.
  (* intros.
  unfold underlying_zipper_set. 
  induction r2; unfold derive, focus; 
    simpl; eauto.
  - (* Void *)
    simpl.
  - (* Epsilon *) 
    destruct (EdelmannGset.nullable r1); simpl; set_solver. *)