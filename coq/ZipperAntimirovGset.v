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
  List.fold_left Regex.Concat ctx Epsilon.

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


(* Mapping [context_to_re] over the singleton zipper containing the empty context
  yields the singleton set containing [Epsilon ]*)
Lemma singleton_empty_ctx_is_singleton_epsilon : 
  @set_map _ _ _ _ _ _ EmptyZipper _ context_to_re ({[ [] ]} : zipper) = 
  ({[ Epsilon ]} : zipper).
Proof.
  unfold set_map. set_solver.  
Qed.  

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



Lemma set_map_singleton_zipper : forall (ctx : context) (f : context -> zipper),
  set_map f ({[ ctx ]} : zipper) = f ctx.
Proof.
  intros.
  unfold set_map. 
  rewrite elements_singleton. simpl. 
  set_solver.
Qed.  

Lemma set_map_singleton_re_gset : forall (ctx : context) (f : context -> re),
  set_map f ({[ ctx ]} : zipper) = ({[ f ctx ]} : gset re).
Proof.
  intros.
  unfold set_map.
  rewrite elements_singleton. simpl. 
  set_solver.
Qed.  

Lemma set_map_singleton_re_re : forall r (f : re -> re),
  set_map f ({[ r ]} : gset re) = ({[ f r ]} : gset re).
Proof.
  intros.
  unfold set_map.
  rewrite elements_singleton. simpl.
  set_solver.
Qed.

(******************************************************************************)

(* The zipper of a union is the union of two zippers *)
Lemma zipper_union_homomorphism : forall (r1 r2 : re) (c : char),
  underlying_zipper_set (Regex.Union r1 r2) c = 
  underlying_zipper_set r1 c ∪ underlying_zipper_set r2 c.
Proof.
  intros.
  unfold underlying_zipper_set. 
  induction r2; unfold derive, focus; 
    cbn; eauto.
  - (* Void *)
    rewrite !zipper_union_empty_r_L.
    rewrite !set_map_singleton_zipper.
Admitted.

(* [zipper_map] and [∪] commutes *)
Lemma zipper_map_union_comm : forall (z1 z2 : zipper) (f : context -> re),
  zipper_map f (z1 ∪ z2) = zipper_map f z1 ∪ zipper_map f z2.
Proof. intros. set_solver. Qed.  

(* TODO: try to prove this *)
Lemma zipper_map_post_compose_concat : forall c r1 r2,
  (zipper_map context_to_re (derive_down c r1 [r2])) =
  set_map (λ r : re, Concat r r2)
    (zipper_map context_to_re (derive_down c r1 [])).
Proof.
  intros. revert c r2.
  induction r1; intros.
  - (* Void *)
    simpl. set_solver.
  - (* Epsilon *)
    simpl. set_solver.
  - (* Atom *)
    unfold derive_down. 
    destruct (c =? c0)%char eqn:E.
    + (* c0 = c *)
      unfold zipper_map.
      rewrite !set_map_singleton_re_gset.
      rewrite empty_context_is_epsilon.
      unfold context_to_re.
      simpl.
      rewrite set_map_singleton_re_re.
      reflexivity.
    + (* c0 <> c *)
      replace (zipper_map context_to_re ∅) with (∅ : gset re) by set_solver.
      set_solver.
  - (* Union *)
    simpl.
    unfold zipper_union. 
    rewrite !zipper_map_union_comm.
    rewrite IHr1_1.
    set_solver.
  - (* Concat *)
    simpl.
    destruct (isEmpty r1_1) eqn:E.
    + (* isEmpty r1_1 = true *)
      unfold zipper_union. 
      rewrite !zipper_map_union_comm.
      destruct r1_1 eqn:E1; simpl.
      * (* r1_1 = Void *)
        set_solver.
      * (* r1_1 = Epsilon *)
        set_solver.
      * (* r1_1 = Atom c *)
        inversion E.
      * (* r1_1 = Union r1 r3 *)
        admit. 
      * (* r1_1 = Concat r1 r3 *)
        inversion E.
        rewrite andb_true_iff in H0. 
        destruct H0 as [H1 H2].
        rewrite H1. 
        admit. 
      * (* r1_1 = Star *)
        admit. (* TODO *)
    + (* isEmpty r1_1 = false *)
      unfold zipper_map.
      admit. (* TODO *) 
  - (* Star *)
    simpl. 
    unfold zipper_map. 
    admit. (* TODO *)
Admitted.    
        

(* The underlying sets for zippers & Antimirov derivatives are equivalent *)
Lemma zipper_antimirov_equivalent : forall (r : re) (c : char),
  underlying_zipper_set r c = underlying_antimirov_set r c.
Proof.
  intros. induction r; unfold underlying_zipper_set, derive, focus.
  - (* Void *)
    cbn. 
    rewrite zipper_union_empty_r_L. 
    rewrite set_map_singleton_zipper.
    simpl. auto.
  - (* Epsilon *) 
    cbn. rewrite zipper_union_empty_r_L. 
    rewrite set_map_singleton_zipper. 
    simpl. auto.
  - (* Atom *)
     cbn.
     destruct (char_dec c c0).
     + (* c = c0 *) 
       unfold focus, derive. simpl. 
       assert ((c =? c0)%char = true).
      { rewrite <- reflect_iff. apply e.
         apply Ascii.eqb_spec. }
      rewrite zipper_union_empty_r_L, set_map_singleton_zipper. simpl.
      rewrite Ascii.eqb_sym.
      rewrite H. simpl. 
      unfold zipper_map.
      rewrite set_map_singleton_re_gset. 
      rewrite empty_context_is_epsilon. reflexivity.
     + (* c <> c0 *)
       simpl. unfold context_to_re.
       unfold focus, derive. simpl.
       assert ((c =? c0)%char = false).
       { rewrite Ascii.eqb_neq. assumption. }
       rewrite zipper_union_empty_r_L, set_map_singleton_zipper. simpl.
       rewrite Ascii.eqb_sym. 
       rewrite H. simpl. set_solver.
  - (* Union *)
    simpl. 
    rewrite set_map_singleton_zipper.
    rewrite <- IHr1, <- IHr2.
    unfold underlying_zipper_set. 
    unfold derive, focus.
    rewrite !set_map_singleton_zipper. 
    unfold derive_up. simpl.
    destruct (isEmpty r1) eqn:E1.
    + (* isEmpty r1 = true *)
      cbn.
      rewrite !zipper_union_empty_r_L.
      destruct (isEmpty r2) eqn:E2; 
        unfold zipper_union;
        apply zipper_map_union_comm.
    + (* isEmpty r1 = false *)
      cbn. 
      destruct (isEmpty r2) eqn:E2; 
        unfold zipper_union;
        rewrite !zipper_union_empty_r_L;
        apply zipper_map_union_comm.
  - (* Concat *)
    simpl.
    rewrite <- IHr1, <- IHr2.
    rewrite set_map_singleton_zipper. 
    destruct (isEmpty r1) eqn:E1. 
    + (* isEmpty r1 = true *)
      simpl. 
      rewrite !zipper_union_empty_r_L.
      rewrite E1. cbn.
      destruct (isEmpty r2) eqn:E2; 
        rewrite zipper_union_empty_r_L.
      * (* isEmpty r2 = true *)
        unfold zipper_union.
        rewrite zipper_map_union_comm. 
        unfold underlying_zipper_set, focus, derive. 
        rewrite !set_map_singleton_zipper.
        cbn.
        rewrite !zipper_union_empty_r_L. 
        rewrite E1, E2.
        rewrite zipper_map_post_compose_concat. reflexivity.
      * (* isEmpty r2 = false *)
        unfold zipper_union.
        rewrite zipper_map_union_comm. 
        unfold underlying_zipper_set, derive, focus.
        rewrite !set_map_singleton_zipper.
        cbn.
        rewrite !zipper_union_empty_r_L. 
        rewrite E1, E2.
        rewrite zipper_map_post_compose_concat.
        reflexivity.
    + (* isEmpty r1 = false *)
      simpl. rewrite E1; cbn.
      rewrite zipper_union_empty_r_L.
      unfold underlying_zipper_set.
      unfold focus, derive.
      rewrite !set_map_singleton_zipper.
      unfold derive_up. 
      rewrite E1. 
      cbn. 
      rewrite zipper_union_empty_r_L. 
      rewrite zipper_map_post_compose_concat.      
      reflexivity.
  - (* Star *)
    simpl. 
    rewrite set_map_singleton_zipper. 
    rewrite <- IHr.
  
   (* Issue: for [Star], [derive_down] just accumulates an increasing list of [r]s :

      derive_up c [Star r]
      === zipper_union (derive_down c (Star r) []) (derive_up c [])
      === zipper_union (derive_down c (Star r) []) ∅ 
      === derive_down c (Star r) []
      === derive down c r [r; Star r]
      === derive down c r [r; r; Star r]
      === ... 
    
    *)
    admit.
Admitted. (* TODO *)  
