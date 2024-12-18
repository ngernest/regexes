Require Export List Ascii Bool.
Import ListNotations.
Require Export Regex Height.
Require Import Regex Edelmann Antimirov.
From stdpp Require Import gmap sets fin_sets.

(** Proving that the underlying sets for zippers & Antimirov derivatives are equivalent *)

(** Maps a function over a zipper, returning a set of regexes *)
Definition zipper_map (f : context -> re) (z : zipper) : gset re :=
  set_map f z.

(** Converts a [context] (used in Edelmann's zipper representation) to a regex 
    by folding the [concat] smart constructor over the context *)
Definition context_to_re (ctx : context) : re :=
  List.fold_left Regex.Concat ctx Epsilon.

(** Empty context corresponds to [Epsilon] *)
Lemma empty_context_is_epsilon : 
  context_to_re [] = Epsilon.
Proof.
  unfold context_to_re. simpl. reflexivity.
Qed.    

(** The underlying regex set that forms the zipper representation of 
    Brozozwski derivatives (from Edelmann's dissertation) *)
Definition underlying_zipper_set (r : re) (c : char) : gset re :=
  zipper_map context_to_re (derive c (focus r)).
  
(** The underlying regex set formed after taking the Antimirov derivative *)
Definition underlying_antimirov_set (r : re) (c : char) : gset re :=
  a_der r c.
  
(** Typeclass instance needed to make [zipper_union_empty_r_L] below typecheck *)
Instance ZipperEmpty : Empty zipper := {
  empty := ∅ 
}.

(** The empty zipper is the right identity for the [zipper_union] operation *)
Lemma zipper_union_empty_r_L : forall (z : zipper),
  zipper_union z ∅ = z.
Proof.
  unfold zipper_union. intros.
  replace (gset_union z ∅) with (z ∪ ∅) by set_solver. 
  set_solver.
Qed.  

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
(** zipper_map and ∪ commute *)
Lemma zipper_map_union_comm : forall (z1 z2 : zipper) (f : context -> re),
  zipper_map f (z1 ∪ z2) = zipper_map f z1 ∪ zipper_map f z2.
Proof. intros. set_solver. Qed.  

(** Mapping over a zipper with λr. Concat r r2 is the same 
    as calling the zipper Brzozowski derivative with r2 appended to 
    the end of the context ctx *)
Lemma zipper_map_post_compose_concat : forall c r1 r2 ctx,
  zipper_map context_to_re (derive_down c r1 (ctx ++ [r2])) =
  set_map (λ r : re, Concat r r2)
    (zipper_map context_to_re (derive_down c r1 ctx)).
Proof.
  intros. revert c r2 ctx.
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
      unfold context_to_re. simpl. 
      induction ctx as [|r ctx' IHctx'].
      * (* ctx = [] *)
        simpl. 
        unfold set_map. 
        rewrite elements_singleton. 
        simpl. 
        set_solver.
      * (* ctx = r :: ctx' *)
        simpl.
        rewrite set_map_singleton_re_re. 
        simpl. 
        rewrite fold_left_app.
        simpl. 
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
    unfold zipper_union.
    destruct (isEmpty r1_1) eqn:E.
    + (* isEmpty r1_1 = true *)    
      rewrite !zipper_map_union_comm.
      rewrite app_comm_cons.
      specialize (IHr1_1 c r2 (r1_2 :: ctx)).
      rewrite IHr1_1.
      specialize (IHr1_2 c r2 ctx).
      rewrite IHr1_2.
      set_solver.
    + (* isEmpty r1_1 = false *)
      rewrite app_comm_cons.
      specialize (IHr1_1 c r2 (r1_2 :: ctx)).
      rewrite IHr1_1.
      reflexivity.
  - (* Star *)
    simpl. 
    rewrite app_comm_cons.
    specialize (IHr1 c r2 (Star r1 :: ctx)).
    rewrite IHr1.
    reflexivity.
Qed.      

(** The underlying sets for zippers & Antimirov derivatives are equivalent *)
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
      destruct (isEmpty r2) eqn:E2.
      * (* isEmpty r2 = true *)
        rewrite zipper_union_empty_r_L.
        unfold zipper_union.
        rewrite zipper_map_union_comm.
        unfold underlying_zipper_set, derive, focus.
        rewrite !set_map_singleton_zipper.
        cbn;
        rewrite !zipper_union_empty_r_L.
        rewrite E1, E2.
        replace [r2] with ([] ++ [r2]). 
        ++ rewrite zipper_map_post_compose_concat.
           reflexivity.
        ++ apply app_nil_l.
      * (* isEmpty r2 = false *)
        rewrite zipper_union_empty_r_L.
        unfold zipper_union.
        rewrite zipper_map_union_comm.
        unfold underlying_zipper_set, derive, focus.
        rewrite !set_map_singleton_zipper.
        cbn;
        rewrite !zipper_union_empty_r_L.
        rewrite E1, E2.
        replace [r2] with ([] ++ [r2]). 
        ++ rewrite zipper_map_post_compose_concat.
           reflexivity.
        ++ apply app_nil_l.
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
      replace [r2] with ([] ++ [r2]). 
      ++ rewrite zipper_map_post_compose_concat.      
         reflexivity.
      ++ apply app_nil_l.
  - (* Star *)
    simpl. 
    rewrite set_map_singleton_zipper. 
    rewrite <- IHr.
    cbn.
    rewrite !zipper_union_empty_r_L.
    unfold underlying_zipper_set, derive, focus. 
    rewrite set_map_singleton_zipper. 
    unfold derive_up. 
    destruct (isEmpty r) eqn:E.
    + (* isEmpty r = true *)
      cbn.
      rewrite !zipper_union_empty_r_L.
      replace [Star r] with ([] ++ [Star r]).
      ++ rewrite zipper_map_post_compose_concat.
         reflexivity.
      ++ apply app_nil_l.
    + (* isEmpty r = false *)
      cbn.
      rewrite !zipper_union_empty_r_L.
      replace [Star r] with ([] ++ [Star r]).
       ++ rewrite zipper_map_post_compose_concat.
          reflexivity.
      ++ apply app_nil_l.
Qed.
