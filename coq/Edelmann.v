(* Adapted from Romain Edelmann's Coq formalisation
   https://github.com/epfl-lara/silex-proofs/blob/master/Zippers.v *)

Require Export List ListSet Ascii Bool.
Require Extraction.
Import ListNotations.

(* Tell Coq to genearate Boolean equality for lists + 
   proof of decidability for list equality *)
Scheme Equality for list.

(***** CHARACTERS AND WORDS *****)

Global Declare Scope char_class_scope.
Open Scope char_class_scope.

(* Input characters. *)
Definition char := ascii.

(* Input words. *)
Definition word := list char.

(***** REGULAR EXPRESSIONS *****)

(* Regular expressions. *)
Inductive regexpr: Type :=
  | Failure
  | Epsilon
  | Character (c: char)
  | Disjunction (l r: regexpr)
  | Sequence (l r: regexpr)
  | Repetition (e: regexpr).

(* Semantics of regular expressions as 
 * a predicate on words.
 *)
Inductive matches: regexpr -> word -> Prop :=
  | MEps : matches Epsilon []
  | MChar (cl: char) (c : char):
      Ascii.eqb cl c = true ->
      matches (Character cl) [c]
  | MDisL (l r: regexpr) (w: word):
      matches l w ->
      matches (Disjunction l r) w
  | MDisR (l r: regexpr) (w: word):
      matches r w ->
      matches (Disjunction l r) w
  | MSeq (l r: regexpr) (wl wr: word):
      matches l wl ->
      matches r wr ->
      matches (Sequence l r) (wl ++ wr)
  | MRepO (e: regexpr):
      matches (Repetition e) []
  | MRepS (e: regexpr) (we wr: word):
      matches e we ->
      matches (Repetition e) wr ->
      matches (Repetition e) (we ++ wr).

Local Hint Constructors matches : matches.

(* Regular expressions can be compared for equality. *)
Lemma regexpr_eq_dec : forall (e1 e2: regexpr),
  {e1 = e2} + {e1 <> e2}.
Proof.
  repeat decide equality.
Qed.

(* Boolean equality for regexes *)
Fixpoint regex_eqb (r1 r2 : regexpr) : bool :=
  match (r1, r2) with 
  | (Failure, Failure) | (Epsilon, Epsilon) =>
      true 
  | (Character c1, Character c2) => 
      Ascii.eqb c1 c2
  | (Disjunction r11 r12, Disjunction r21 r22) 
  | (Sequence r11 r12, Sequence r21 r22) => 
      regex_eqb r11 r21 && regex_eqb r21 r22
  | (Repetition r1', Repetition r2') => regex_eqb r1' r2'
  | (_, _) => false 
  end.


(* Unfold one non-empty instance from
 * a Repetition's matches.
 *)
Lemma MRep1 : forall e w,
  matches (Repetition e) w ->
  w <> [] ->
  exists w1 w2,
    w = w1 ++ w2 /\
    w1 <> [] /\
    matches e w1 /\
    matches (Repetition e) w2.
Proof.
  intros.
  remember (Repetition e) as re in H.
  induction H; inversion Heqre.
  { contradiction. }
  subst.
  destruct we eqn:W.
  - simpl in *.
    apply IHmatches2; eauto.
  - exists we, wr.
    repeat split; subst; eauto.
    intros A. inversion A.
Qed.

(* Does the expression e accept the empty string? *)
Fixpoint nullable (e: regexpr) : bool :=
  match e with
  | Failure => false
  | Epsilon => true
  | Character _ => false
  | Disjunction l r => orb (nullable l) (nullable r)
  | Sequence l r => andb (nullable l) (nullable r)
  | Repetition _ => true
  end.

(* Computation of nullable is correct with respect to semantics. *)
Theorem nullable_matches : forall e,
  nullable e = true <-> matches e [].
Proof.
  induction e; split; intros; simpl in *; eauto with matches.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - apply Bool.orb_true_iff in H.
    destruct H.
    + apply MDisL. apply IHe1. assumption.
    + apply MDisR. apply IHe2. assumption.
  - inversion H; subst; apply Bool.orb_true_iff.
    + left. apply IHe1. assumption.
    + right. apply IHe2. assumption.
  - apply Bool.andb_true_iff in H as [H1 H2].
    rewrite <- app_nil_l.
    constructor.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
  - apply Bool.andb_true_iff.
    inversion H; subst.
    apply app_eq_nil in H2 as [LN RN]; subst.
    split.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
Qed.

(***** CONTEXTS AND ZIPPERS *****)

(* Contexts are sequences of regular expressions. *)
Definition context := list regexpr.

(* The semantics of contexts. *)
Inductive context_matches : context -> word -> Prop :=
  | MCNil : context_matches [] []
  | MCCons e ctx we wctx :
    matches e we ->
    context_matches ctx wctx ->
    context_matches (e :: ctx) (we ++ wctx).

Local Hint Constructors context_matches : context_matches.

(* Contexts can be compared for equality. *)
Lemma context_eq_dec : forall (ctx1 ctx2: context),
  {ctx1 = ctx2} + {ctx1 <> ctx2}.
Proof.
  repeat decide equality.
Qed.

(* Boolean equality for contexts *)
Definition context_eqb (xs : context) (ys : context) : bool := 
  list_beq regexpr regex_eqb xs ys.


(* Find the first non-empty instance given a context's match. *)
Lemma context_matches_non_empty : forall ctx w,
  context_matches ctx w ->
  w <> [] ->
  exists ctx1 e ctx2 we wctx2,
    ctx = ctx1 ++ (e :: ctx2) /\
    w = we ++ wctx2 /\
    we <> [] /\
    (forall e0, In e0 ctx1 -> matches e0 []) /\
    matches e we /\
    context_matches ctx2 wctx2.
Proof.
  intros ctx w H.
  induction H; intros.
  - contradiction.
  - destruct we.
    + simpl in *.
      specialize (IHcontext_matches H1) as [ctx1 [e' [ctx2 [we [wctx2 C]]]]].
      destruct C as [Eqctx [Eqw [Ne [N1 [Me' MC]]]]].
      exists (e :: ctx1), e', ctx2, we, wctx2.
      repeat split.
      * subst. simpl. reflexivity.
      * assumption.
      * assumption.
      * intros. inversion H2; subst.
        { assumption. }
        apply N1. assumption.
      * assumption.
      * assumption.
    + exists [], e, ctx, (c :: we), wctx.
      repeat split.
      * intros A. inversion A.
      * intros e0 A. inversion A.
      * assumption.
      * assumption.
Qed.

(* Zippers are disjunctions of contexts. *)
Definition zipper := set context.

(* The semantics of zippers. *)
Definition zipper_matches z w : Prop :=
  exists ctx, set_In ctx z /\ context_matches ctx w.

(* Disjunction of two zippers. *)
Definition zipper_union := set_union context_eq_dec.

(* Addition of a context in a zipper. *)
Definition zipper_add := set_add context_eq_dec.

(* Convert a regular expression into a zipper. *)
Definition focus (e: regexpr): zipper := [[e]].

(* Correctness of focus. *)
Theorem focus_correct : forall e w,
  matches e w <-> zipper_matches (focus e) w.
Proof.
  unfold focus, zipper_matches; intros.
  split; intros.
  - exists [e]. split.
    + left. reflexivity.
    + rewrite <- app_nil_r.
      apply MCCons; eauto with context_matches.
  - destruct H as [ctx [I M]].
    inversion M; inversion I; subst.
    + inversion H1.
    + inversion H1.
    + inversion H3; subst.
      inversion H0; subst.
      rewrite app_nil_r.
      assumption.
    + inversion H3.
Qed.

(* Conversion from zipper back to regexpr. 
 * Unused, but provides some intuition on zippers.
 *)
Definition unfocus (z: zipper): regexpr :=
  let ds := map (fun ctx => fold_right Sequence Epsilon ctx) z in
  fold_right Disjunction Failure ds.

(* Correctness of unfocus. *)
Theorem unfocus_correct : forall z w,
  zipper_matches z w <-> matches (unfocus z) w.
Proof.
  split.
  - intros. destruct H as [ctx [I M]].
    unfold unfocus.
    induction z; inversion I; subst; simpl in *.
    + apply MDisL.
      clear I IHz z.
      generalize dependent w.
      induction ctx; intros; inversion M; subst; simpl; constructor.
      * assumption.
      * apply IHctx. assumption.
    + apply MDisR.
      apply IHz.
      apply H.
  - generalize dependent w.
    unfold unfocus.
    induction z; intros; simpl in *; inversion H; subst.
    + exists a.
      split.
      * left. reflexivity.
      * clear IHz H z.
        generalize dependent w.
        induction a; intros; simpl in *; inversion H3; subst.
        { constructor. }
        constructor; try assumption.
        apply IHa. assumption.
    + specialize (IHz w H3).
      destruct IHz as [ctx [I M]].
      exists ctx.
      split.
      * right. assumption.
      * assumption.
Qed.

Theorem unfocus_focus :
  forall e w,
    matches (unfocus (focus e)) w <-> matches e w.
Proof.
  intros e w.
  rewrite <- unfocus_correct.
  rewrite <- focus_correct.
  reflexivity.
Qed.

(***** DERIVATION *****)

(* Downwards phase of Brzozowski's derivation on zippers. *)
Fixpoint derive_down (c: char) (e: regexpr) (ctx: context): zipper :=
  match e with
  | Character cl => if Ascii.eqb cl c then [ctx] else []
  | Disjunction l r => zipper_union (derive_down c l ctx) (derive_down c r ctx)
  | Sequence l r => if (nullable l)
    then
      zipper_union (derive_down c l (r :: ctx)) (derive_down c r ctx)
    else
      derive_down c l (r :: ctx)
  | Repetition e' => derive_down c e' (e :: ctx) 
  | _ => []
  end.

(* Upwards phase of Brzozowski's derivation on zippers. *)
Fixpoint derive_up (c: char) (ctx: context): zipper :=
  match ctx with
  | [] => []
  | e :: ctx' => if nullable e
    then 
      zipper_union (derive_down c e ctx') (derive_up c ctx')
    else
      derive_down c e ctx'
  end.

(* Brzozowski's derivation on zippers. *)
Definition derive (c: char) (z: zipper): zipper :=
  fold_right zipper_union [] (map (derive_up c) z).

(* Soundness of the downwards phase. *)
Lemma derive_down_sound : forall e ctx c w,
  zipper_matches (derive_down c e ctx) w ->
  exists we wctx,
    w = we ++ wctx /\
    matches e (c :: we) /\
    context_matches ctx wctx.
Proof.
  induction e; intros; simpl in *; destruct H as [ctx' [I' M']].
  + inversion I'.
  + inversion I'.
  + destruct ((c =? c0)%char) eqn:N.
    - subst.
      exists [], w.
      repeat split.
      * constructor. assumption.
      * inversion I'; subst.
        { assumption. }
        inversion H.
    - inversion I'.
  + apply set_union_elim in I' as [IL | IR].
    - unshelve epose proof IHe1 ctx c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      exists we, wctx.
      repeat split.
      * assumption.
      * apply MDisL. assumption.
      * assumption.
    - unshelve epose proof IHe2 ctx c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      exists we, wctx.
      repeat split.
      * assumption.
      * apply MDisR. assumption.
      * assumption.
  + destruct (nullable e1) eqn:N.
    apply set_union_elim in I' as [IL | IR].
    - unshelve epose proof IHe1 (e2 :: ctx) c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      inversion MC; subst.
      exists (we ++ we0), wctx0.
      repeat split.
      * rewrite app_assoc. reflexivity.
      * rewrite app_comm_cons.
        apply MSeq; assumption.
      * assumption.
    - unshelve epose proof IHe2 ctx c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      exists we, wctx.
      repeat split.
      * assumption.
      * rewrite <- app_nil_l.
        apply MSeq.
        { apply nullable_matches. assumption. }
        assumption.
      * assumption.
    - unshelve epose proof IHe1 (e2 :: ctx) c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      inversion MC; subst.
      exists (we ++ we0), wctx0.
      repeat split.
      * rewrite app_assoc. reflexivity.
      * rewrite app_comm_cons.
        apply MSeq; assumption.
      * assumption.
  + unshelve epose proof IHe (Repetition e :: ctx) c w _.
    { exists ctx'. split; assumption. }
    destruct H as [we [wctx [Eqw [Me MC]]]].
    inversion MC; subst.
    exists (we ++ we0), wctx0.
    repeat split.
    - rewrite app_assoc. reflexivity.
    - rewrite app_comm_cons. apply MRepS; assumption.
    - assumption.
Qed.

(* Soundness of the upwards phase. *)
Lemma derive_up_sound : forall ctx c w,
  zipper_matches (derive_up c ctx) w ->
  context_matches ctx (c :: w).
Proof.
  induction ctx; intros; simpl in *.
  { destruct H as [ctx' [A _]]. inversion A. }
  destruct H as [ctx' [I' M']].
  destruct (nullable a) eqn:N.
  + apply set_union_elim in I' as [IL | IR].
    - unshelve epose proof derive_down_sound a ctx c w _.
      { exists ctx'. split; assumption. }
      destruct H as [we [wctx [Eqw [Me MC]]]].
      subst.
      rewrite app_comm_cons.
      apply MCCons; assumption.
    - unshelve epose proof IHctx c w _.
      { exists ctx'. split; assumption. }
      rewrite <- app_nil_l.
      apply MCCons.
      * apply nullable_matches; assumption.
      * assumption.
  + unshelve epose proof derive_down_sound a ctx c w _.
    { exists ctx'. split; assumption. }
    destruct H as [we [wctx [Eqw [Me MC]]]].
    subst.
    rewrite app_comm_cons.
    apply MCCons; assumption.
Qed.

(* Soundness of derivation.
 *
 * When a derivative of a zipper by a character matches a word,
 * the original zipper matches that word prefixed
 * by that character.
 *)
Lemma derive_sound : forall z c w,
  zipper_matches (derive c z) w ->
  zipper_matches z (c :: w).
Proof.
  induction z; intros;
  destruct H as [ctx' [I' M']];
  unfold derive in *; simpl in *;
  try contradiction.
  apply set_union_elim in I' as [IL | IR].
  + unshelve epose proof derive_up_sound a c w _.
    { exists ctx'. split; assumption. }
    exists a.
    split.
    - left. reflexivity.
    - assumption.
  + unshelve epose proof IHz c w _.
    { exists ctx'. split; assumption. }
    destruct H as [ctx [I M]].
    exists ctx.
    split.
    - right. assumption.
    - assumption.
Qed. 

(* Completeness of the downwards phase. *)
Lemma derive_down_complete : forall e ctx c we wctx,
  matches e (c :: we) ->
  context_matches ctx wctx ->
  zipper_matches (derive_down c e ctx) (we ++ wctx).
Proof.
  induction e; intros.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    simpl. rewrite H3.
    unfold zipper_matches.
    exists ctx. split.
    + left. reflexivity.
    + assumption.
  - simpl.
    inversion H; subst.
    + specialize (IHe1 ctx c we wctx H4 H0).
      unfold zipper_matches in IHe1.
      destruct IHe1 as [ctx' [I' M']].
      exists ctx'.
      split.
      * apply set_union_intro1. assumption.
      * assumption.
    + specialize (IHe2 ctx c we wctx H4 H0).
      unfold zipper_matches in IHe2.
      destruct IHe2 as [ctx' [I' M']].
      exists ctx'.
      split.
      * apply set_union_intro2. assumption.
      * assumption.
  - inversion H; subst.
    destruct wl.
    + simpl.
      assert (N: nullable e1 = true).
      { apply nullable_matches. assumption. }
      rewrite N.
      simpl in *.
      subst.
      specialize (IHe2 ctx c we wctx H5 H0).
      destruct IHe2 as [ctx' [I' M']].
      exists ctx'.
      split.
      * apply set_union_intro2. assumption.
      * assumption.
    + simpl.
      unshelve epose proof (IHe1 (e2 :: ctx) c0 wl (wr ++ wctx) H4 _).
      { apply MCCons; assumption. }
      destruct H1 as [ctx' [I' M']].
      exists ctx'.
      simpl in H3.
      inversion H3.
      subst.
      split.
      { destruct (nullable e1).
        - apply set_union_intro1. apply I'.
        - apply I'.
      }
      rewrite <- app_assoc.
      apply M'.
  - simpl.
    apply MRep1 in H.
    + destruct H as [w1 [w2 [Eqw [Nn1 [M1 M2]]]]].
      destruct w1.
      { contradiction. }
      simpl in Eqw.
      inversion Eqw; subst.
      unshelve epose proof (IHe (Repetition e :: ctx) c0 w1 (w2 ++ wctx) M1 _).
      { apply MCCons; assumption. }
      rewrite <- app_assoc.
      apply H.
    + intros A. inversion A.
Qed.

(* Completeness of the upwards phase. *)
Lemma derive_up_complete : forall ctx c w,
  context_matches ctx (c :: w) ->
  zipper_matches (derive_up c ctx) w.
Proof.
  induction ctx; intros; inversion H; subst.
  destruct we.
  { simpl in *.
    destruct (nullable a) eqn:N.
    + subst.
      specialize (IHctx c w H4) as [ctx' [I' M']].
      exists ctx'.
      split.
      - apply set_union_intro2. assumption.
      - assumption.
    + rewrite <- nullable_matches in H3.
      rewrite H3 in N.
      inversion N. }
  inversion H2.
  subst.
  simpl.
  pose proof derive_down_complete a ctx c we wctx H3 H4.
  destruct H0 as [ctx' [I' M']].
  exists ctx'.
  destruct (nullable a) eqn:N.
  + split.
    - apply set_union_intro1. assumption.
    - assumption.
  + split; assumption.
Qed.

(* Completeness of derivation.
 *
 * When a derivative of a zipper by a character matches a word,
 * the original zipper matches that word prefixed
 * by that character.
 *)
Lemma derive_complete : forall z c w,
  zipper_matches z (c :: w) ->
  zipper_matches (derive c z) w.
Proof.
  induction z; intros;
  destruct H as [ctx [I M]].
  { inversion I. }
  inversion I; subst.
  - pose proof derive_up_complete ctx c w M.
    destruct H as [ctx' [I' H']].
    exists ctx'.
    split.
    + unfold derive.
      simpl.
      apply set_union_intro1.
      assumption.
    + assumption.
  - unshelve epose proof IHz c w _.
    { exists ctx. split; assumption. }
    destruct H0 as [ctx' [I' M']].
    exists ctx'.
    split.
    + unfold derive. simpl.
      apply set_union_intro2.
      apply I'.
    + assumption.
Qed.

(* Correctness of derivation. *)
Theorem derive_correct : forall z c w,
  zipper_matches z (c :: w) <->
  zipper_matches (derive c z) w.
Proof.
  intuition auto;
  eauto using derive_sound, derive_complete.
Qed.

Theorem derive_correct_unfocus:
  forall z c w,
    matches (unfocus (derive c z)) w <->
    matches (unfocus z) (c :: w).
Proof.
  intros.
  repeat rewrite <- unfocus_correct.
  split; apply derive_correct.
Qed.

(* Generalisation of derivatives to words. *)
Fixpoint derive_word w z :=
   match w with
   | [] => z
   | c :: w' => derive_word w' (derive c z)
   end.

(* Correctness of derivation generalised to words. *)
Theorem derive_word_correct : forall z w1 w2,
  zipper_matches z (w1 ++ w2) <->
  zipper_matches (derive_word w1 z) w2.
Proof.
  intros z w1.
  generalize dependent z.
  induction w1; intros; simpl in *.
  { reflexivity. }
  split; intros.
  + apply IHw1. apply derive_correct. assumption.
  + apply derive_correct. apply IHw1. assumption.
Qed.

Theorem derive_word_correct_unfocus:
  forall z w1 w2,
    matches (unfocus (derive_word w1 z)) w2 <->
    matches (unfocus z) (w1 ++ w2).
Proof.
  intros.
  repeat rewrite <- unfocus_correct.
  split; apply derive_word_correct.
Qed.

(* Does the zipper z accept the empty word? *)
Definition zipper_nullable z : bool :=
  existsb (fun ctx => forallb nullable ctx) z.

(* Correctness of nullability checks on zippers. *)
Theorem zipper_nullable_correct : forall z,
  zipper_nullable z = true <->
  zipper_matches z [].
Proof.
  intros z.
  split.
  - intros.
    unfold zipper_nullable in H.
    rewrite existsb_exists in H.
    destruct H as [ctx [I F]].
    rewrite forallb_forall in F.
    exists ctx.
    split.
    { assumption. }
    clear I. clear z.
    induction ctx; intros.
    + apply MCNil.
    + rewrite <- app_nil_l.
      apply MCCons.
      * apply nullable_matches.
        apply F. left. reflexivity.
      * apply IHctx.
        intros e H. apply F. right. assumption.
  - intros. destruct H as [ctx [I M]].
    unfold zipper_nullable.
    rewrite existsb_exists.
    exists ctx.
    split.
    { assumption. }
    clear I. clear z.
    remember [] as w in M.
    induction M.
    + simpl. reflexivity.
    + simpl. rewrite Bool.andb_true_iff.
      apply app_eq_nil in Heqw as [W WC].
      subst.
      split.
      * apply nullable_matches. assumption.
      * apply IHM; eauto.
Qed.

Theorem nullable_correct_unfocus:
  forall z,
    zipper_nullable z = true <->
    matches (unfocus z) [].
Proof.
  intros.
  rewrite <- unfocus_correct.
  split; apply zipper_nullable_correct.
Qed.

(* Does the zipper z accept the word w? *)
Definition zipper_accepts (z : zipper) (w : word) : bool :=
  zipper_nullable (derive_word w z).

(* Correctness of the zipper recogniser. *)
Theorem zipper_accepts_correct : forall z w,
  zipper_accepts z w = true <->
  zipper_matches z w.
Proof.
  intros.
  unfold zipper_accepts.
  rewrite zipper_nullable_correct.
  pose proof derive_word_correct z w [].
  rewrite app_nil_r in H.
  symmetry.
  apply H.
Qed.

(* Does the regular expression e accept the word w?
 * Finds out using zippers!
 *)
Definition accepts (e : regexpr) (w : list char) : bool :=
  zipper_accepts (focus e) w.

(* Unit test: does the character literal ['c'] match [Character 'c']? *)
(* Compute (accepts (Character "c"%char) ["c"%char]). *)

(* Correctness of the zipper-based recogniser. *)
Theorem accepts_correct : forall e w,
  accepts e w = true <->
  matches e w.
Proof.
  intros.
  rewrite focus_correct.
  unfold accepts.
  apply zipper_accepts_correct.
Qed.

(***** FINITENESS *****)

(* Downwards phase of the maximal zipper. *)
Fixpoint max_zipper_down (e: regexpr) (ctx: context): set context :=
  match e with
  | Character _ => [ctx]
  | Disjunction l r => zipper_union (max_zipper_down l ctx) (max_zipper_down r ctx)
  | Sequence l r => zipper_union (max_zipper_down l (r :: ctx)) (max_zipper_down r ctx)
  | Repetition e' => max_zipper_down e' (e :: ctx)
  | _ => []
  end.

(* Upwards phase of the maximal zipper. *)
Fixpoint max_zipper_up (ctx: context): set context :=
  match ctx with
  | [] => []
  | e :: ctx' => zipper_union (max_zipper_down e ctx') (max_zipper_up ctx')
  end.

(* Maximal zipper. We shall prove that all derivatives are subsets of this. *)
Definition max_zipper (z: zipper): set context :=
  fold_right zipper_union [] (map max_zipper_up z).

(* Derivation's downwards phase's result is included as part of the
 * maximal zipper computation's downwards phase's result.
 *)
Lemma derive_max_zipper_down_incl : forall e ectx ctx c,
  set_In ctx (derive_down c e ectx) -> set_In ctx (max_zipper_down e ectx).
Proof.
  induction e; intros; simpl in *; try contradiction.
  - destruct ((c =? c0)%char); inversion H; subst.
    + left. reflexivity.
    + inversion H0.
  - apply set_union_elim in H as [H | H].
    + apply set_union_intro1. apply IHe1 with c. assumption.
    + apply set_union_intro2. apply IHe2 with c. assumption.
  - destruct (nullable e1) eqn:N.
    apply set_union_elim in H as [H | H].
    + apply set_union_intro1. apply IHe1 with c. assumption.
    + apply set_union_intro2. apply IHe2 with c. assumption.
    + apply set_union_intro1. apply IHe1 with c. assumption.
  - apply IHe with c. assumption.
Qed.

(* Derivation's upwards phase's result is included as part of the
 * maximal zipper computation's upwards phase's result.
 *)
Lemma derive_max_zipper_up_incl : forall ectx ctx c,
  set_In ctx (derive_up c ectx) -> set_In ctx (max_zipper_up ectx).
Proof.
  induction ectx; intros; simpl in *; try contradiction.
  destruct (nullable a) eqn:N.
  apply set_union_elim in H as [H | H].
  - apply set_union_intro1.
    apply derive_max_zipper_down_incl with c.
    assumption.
  - apply set_union_intro2.
    apply IHectx with c.
    assumption.
  - apply set_union_intro1.
    apply derive_max_zipper_down_incl with c.
    assumption.
Qed.

(* A zipper's (single-step) derivatives are included in its maximal zipper. *)
Theorem derive_max_zipper_incl : forall z c ctx,
  set_In ctx (derive c z) -> set_In ctx (max_zipper z).
Proof.
  induction z; intros; simpl in *; try contradiction.
  unfold derive in *.
  unfold max_zipper.
  simpl in *.
  apply set_union_elim in H as [H | H].
  + apply set_union_intro1.
    apply derive_max_zipper_up_incl with c. 
    assumption.
  + apply set_union_intro2.
    apply IHz with c.
    assumption.
Qed.

(* Lemma on membership in a mapped zipper addition. *)
Lemma map_zipper_add {A} :
forall z f (x : A) ctx,
  In x (map f (zipper_add ctx z)) ->
  (f ctx = x \/ In x (map f z)).
Proof.
  induction z; intros; simpl in *.
  - assumption.
  - destruct (context_eq_dec ctx a); subst.
    + inversion H.
      * left. assumption.
      * right. right. assumption.
    + simpl in *.
      inversion H.
      * right. left. assumption.
      * specialize (IHz f x ctx H0) as [I | I];
        eauto.
Qed.

(* Lemma on membership in a mapped zipper union. *)
Lemma map_zipper_union {A} :
  forall z1 z2 f (x : A),
    In x (map f (zipper_union z1 z2)) ->
    (In x (map f z1) \/ In x (map f z2)).
Proof.
  intros z1 z2.
  generalize dependent z1.
  induction z2; intros; simpl in *.
  + left. assumption.
  + apply map_zipper_add in H as [H | H].
    - right. left. assumption.
    - specialize (IHz2 z1 f x H) as [I | I]; eauto.
Qed.

(* Elimination of unions of zippers. *)
Lemma zippers_union_elim :
  forall zs ctx,
    set_In ctx (fold_right zipper_union [] zs) ->
    exists z,
      In z zs /\
      set_In ctx z.
Proof.
  induction zs; intros; simpl in *; try contradiction.
  apply set_union_elim in H as [H | H].
  - exists a. split.
    + left. reflexivity.
    + assumption.
  - specialize (IHzs ctx H) as [z [I1 I2]].
    exists z. split.
    + right. assumption.
    + assumption.
Qed.

(* Introduction of unions of zippers. *)
Lemma zippers_union_intro :
  forall zs z ctx,
    In z zs ->
    set_In ctx z ->
    set_In ctx (fold_right zipper_union [] zs).
Proof.
  induction zs; intros; simpl in *; try contradiction.
  destruct H as [H | H]; subst.
  - apply set_union_intro1. assumption.
  - specialize (IHzs z ctx H H0).
    apply set_union_intro2. assumption.
Qed.

(* Monotonicity of the maximal zipper's upwards phase
 * with respect to (single-step) derivation.
 *)
Theorem derive_max_zipper_down_mono : forall e ectx ctx c,
  set_In ctx (max_zipper (derive_down c e ectx)) ->
  set_In ctx (max_zipper [e :: ectx]).
Proof.
  induction e; intros; simpl in *; try contradiction.
  - destruct ((c =? c0)%char); subst; simpl in *.
    + unfold max_zipper in *.
      simpl in *.
      apply set_union_intro2. apply H.
    + contradiction.
  - unfold max_zipper in H.
    apply zippers_union_elim in H as [z [I1 I2]].
    apply map_zipper_union in I1 as [I1 | I1].
    + unshelve epose proof IHe1 ectx ctx c _.
      { apply zippers_union_intro with z; assumption. }
      unfold max_zipper in H.
      apply zippers_union_elim in H as [z' [I1' I2']].
      destruct I1' as [I1' | A]; try contradiction.
      subst.
      simpl in I2'.
      unfold max_zipper. simpl.
      apply set_union_elim in I2' as [I2' | I2'].
      * apply set_union_intro1. apply set_union_intro1.
        assumption.
      * apply set_union_intro2. assumption.
    + unshelve epose proof IHe2 ectx ctx c _.
      { apply zippers_union_intro with z; assumption. }
      unfold max_zipper in H.
      apply zippers_union_elim in H as [z' [I1' I2']].
      destruct I1' as [I1' | A]; try contradiction.
      subst.
      simpl in I2'.
      unfold max_zipper. simpl.
      apply set_union_elim in I2' as [I2' | I2'].
      * apply set_union_intro1. apply set_union_intro2.
        assumption.
      * apply set_union_intro2. assumption.
  - unfold max_zipper in H.
    destruct (nullable e1) eqn:N.
    + apply zippers_union_elim in H as [z [I1 I2]].
      apply map_zipper_union in I1 as [I1 | I1].
      * unshelve epose proof IHe1 (e2 :: ectx) ctx c _.
        { unfold max_zipper.
          apply zippers_union_intro with z; assumption. }
        unfold max_zipper in H.
        unfold max_zipper.
        simpl in *.
        apply set_union_elim in H as [H | H].
        { apply set_union_intro1.
          apply set_union_intro1.
          assumption. }
        apply set_union_elim in H as [H | H].
        { apply set_union_intro1.
          apply set_union_intro2.
          assumption. }
        apply set_union_intro2.
        assumption.
      * unshelve epose proof IHe2 ectx ctx c _.
        { unfold max_zipper.
          apply zippers_union_intro with z; assumption. }
        unfold max_zipper in H.
        unfold max_zipper.
        simpl in *.
        apply set_union_elim in H as [H | H].
        { apply set_union_intro1.
          apply set_union_intro2.
          assumption. }
        apply set_union_intro2.
        assumption.
    + apply zippers_union_elim in H as [z [I1 I2]].
      unshelve epose proof IHe1 (e2 :: ectx) ctx c _.
      { unfold max_zipper.
        apply zippers_union_intro with z; assumption. }
      unfold max_zipper in H.
      unfold max_zipper.
      simpl in *.
      apply set_union_elim in H as [H | H].
      { apply set_union_intro1.
        apply set_union_intro1.
        assumption. }
      apply set_union_elim in H as [H | H].
      { apply set_union_intro1.
        apply set_union_intro2.
        assumption. }
      apply set_union_intro2.
      assumption.
  - unfold max_zipper in H.
    apply zippers_union_elim in H as [z [I1 I2]].
    unfold max_zipper.
    unshelve epose proof IHe (Repetition e :: ectx) ctx c _.
    { unfold max_zipper.
      apply zippers_union_intro with z; assumption. }
    unfold max_zipper in H. simpl in H.
    apply set_union_elim in H as [H | H].
    { simpl. apply set_union_intro1. assumption. }
    apply set_union_elim in H as [H | H].
    { simpl. apply set_union_intro1. assumption. }
    simpl.
    apply set_union_intro2.
    assumption.
Qed.

(* Monotonicity of the maximal zipper's downwards phase
 * with respect to (single-step) derivation.
 *)
Theorem derive_max_zipper_up_mono : forall ectx ctx c,
  set_In ctx (max_zipper (derive_up c ectx)) ->
  set_In ctx (max_zipper [ectx]).
Proof.
  induction ectx; intros; simpl in *; try contradiction.
  destruct (nullable a) eqn:N.
  + unfold max_zipper in H.
    apply zippers_union_elim in H as [z [I1 I2]].
    apply map_zipper_union in I1 as [I1 | I1].
    - unshelve epose proof derive_max_zipper_down_mono a ectx ctx c _.
      { unfold max_zipper.
        apply zippers_union_intro with z; assumption. }
      assumption.
    - unshelve epose proof IHectx ctx c _.
      { unfold max_zipper.
        apply zippers_union_intro with z; assumption. }
      unfold max_zipper.
      simpl.
      apply set_union_intro2.
      apply H.
  + unfold max_zipper in H.
    apply zippers_union_elim in H as [z [I1 I2]].
    unshelve epose proof derive_max_zipper_down_mono a ectx ctx c _.
    { unfold max_zipper.
      apply zippers_union_intro with z; assumption. }
    assumption.
Qed.

(* Monotonicity of the maximal zipper with respect to (single-step) derivation. *)
Theorem derive_max_zipper_mono : forall z c ctx,
  set_In ctx (max_zipper (derive c z)) -> set_In ctx (max_zipper z).
Proof.
  induction z; intros; simpl in *; try contradiction.
  unfold derive in H.
  simpl in H.
  unfold max_zipper in H.
  apply zippers_union_elim in H as [z' [I1 I2]].
  apply map_zipper_union in I1 as [I1 | I1].
  + unshelve epose proof derive_max_zipper_up_mono a ctx c _.
    { apply zippers_union_intro with z'; assumption. }
    unfold max_zipper in *.
    simpl in *.
    apply set_union_intro1.
    assumption.
  + unshelve epose proof IHz c ctx _.
    { apply zippers_union_intro with z'; assumption. }
    unfold max_zipper.
    simpl.
    apply set_union_intro2.
    unfold max_zipper in H.
    apply zippers_union_elim in H as [z'' [I1' I2']].
    apply zippers_union_intro with z''; try assumption.
Qed.

(* Contexts of generalised derivatives of a zipper are contexts
 * of the maximal zipper of that initial zipper.
 *)
Theorem derive_word_max_zipper : forall z w ctx,
  w <> [] ->
  set_In ctx (derive_word w z) -> set_In ctx (max_zipper z).
Proof.
  intros z w.
  generalize dependent z.
  destruct w.
  { intros. exfalso. apply H. reflexivity. }
  generalize dependent c.
  induction w; intros.
  { simpl in H0.
    apply derive_max_zipper_incl in H0.
    assumption.
  }
  clear H.
  remember (a :: w) as aw in *.
  simpl in H0.
  subst.
  apply IHw in H0.
  { apply derive_max_zipper_mono with c. assumption. }
  intros A. inversion A.
Qed.

(* Finiteness theorem. For any zipper z, there exists a set of contexts Z 
 * such that, for any generalised derivative of z,
 * that derivative's contexts are all part of the set of contexts Z.
 *)
Theorem finiteness:
  forall z,
  exists Z,
  forall w,
  forall ctx,
  set_In ctx (derive_word w z) ->
  set_In ctx Z.
Proof.
  intros z.
  exists (zipper_union z (max_zipper z)).
  destruct w; intros; simpl in *.
  { apply set_union_intro1. assumption. }
  apply set_union_intro2.
  apply derive_word_max_zipper with (c :: w).
  { intros A. inversion A. }
  assumption.
Qed.

Fixpoint productive e :=
  match e with
  | Epsilon => true
  | Failure => false
  | Character _ => true
  | Disjunction l r => orb (productive l) (productive r)
  | Sequence l r => andb (productive l) (productive r)
  | Repetition _ => true
  end.

Lemma productive_complete :
  forall e,
    (exists w, matches e w) ->
    productive e = true.
Proof.
  induction e; intros; destruct H as [w M]; simpl.
  - inversion M.
  - reflexivity.
  - reflexivity.
  - apply Bool.orb_true_iff.
    inversion M; subst.
    + left. apply IHe1. exists w. assumption.
    + right. apply IHe2. exists w. assumption.
  - inversion M; subst.
    apply Bool.andb_true_iff.
    split.
    + apply IHe1. exists wl. assumption.
    + apply IHe2. exists wr. assumption.
  - reflexivity.
Qed.

Fixpoint has_first e :=
  match e with
  | Epsilon => false
  | Failure => false
  | Character _ => true
  | Disjunction l r => orb (has_first l) (has_first r)
  | Sequence l r => orb
    (andb (has_first l) (productive r))
    (andb (nullable l) (has_first r))
  | Repetition e => has_first e
  end.

Lemma has_first_productive_nullable :
  forall e,
    productive e = orb (nullable e) (has_first e).
Proof.
  induction e; try reflexivity;
  simpl; rewrite IHe1, IHe2;
  destruct (nullable e1);
  destruct (nullable e2);
  destruct (has_first e1);
  destruct (has_first e2);
  reflexivity.
Qed.

Lemma has_first_complete :
  forall e,
    (exists c w, matches e (c :: w)) ->
    has_first e = true.
Proof.
  induction e; intros; destruct H as [c' [w M]]; simpl.
  - inversion M.
  - inversion M.
  - reflexivity.
  - apply Bool.orb_true_iff.
    inversion M; subst.
    + left. apply IHe1. exists c', w. assumption.
    + right. apply IHe2. exists c', w. assumption.
  - rewrite Bool.orb_true_iff.
    repeat rewrite Bool.andb_true_iff.
    inversion M; subst.
    destruct wl.
    + right. split.
      * apply nullable_matches. assumption.
      * apply IHe2. exists c', w.
        simpl in H1; subst.
        assumption.
    + left. simpl in H1. inversion H1; subst. split.
      * apply IHe1.
        exists c', wl.
        assumption.
      * apply productive_complete.
        exists wr.
        assumption.
  - apply MRep1 in M as [w1 [w2 [E [N [M1 M2]]]]].
    + apply IHe.
      destruct w1.
      { contradiction. }
      inversion E; subst.
      exists c, w1. assumption.
    + intros A. inversion A.
Qed.

Definition has_first_zipper z := 
  existsb (fun ctx => andb
    (forallb productive ctx)
    (existsb has_first ctx)) z.

Theorem has_first_zipper_complete :
  forall z,
    (exists c w, zipper_matches z (c :: w)) ->
    has_first_zipper z = true.
Proof.
  intros.
  destruct H as [c [w M]].
  destruct M as [ctx [I M]].
  unfold has_first_zipper.
  apply existsb_exists.
  exists ctx.
  split. { apply I. }
  apply Bool.andb_true_iff.
  clear I z.
  unshelve epose proof context_matches_non_empty ctx (c :: w) M _.
  { intros A. inversion A. }
  destruct H as [ctx1 [e [ctx2 [we [wctx2 [Ectx [Ew [Ne [M1 [Me M2]]]]]]]]]].
  rewrite Ectx, forallb_app, existsb_app.
  simpl.
  repeat rewrite Bool.andb_true_iff.
  repeat split.
  + apply forallb_forall. intros e1 I1.
    apply productive_complete.
    exists [].
    apply M1. apply I1.
  + apply productive_complete.
    exists we. apply Me.
  + apply forallb_forall.
    intros e2 I2.
    clear Me M1 Ne Ew Ectx we e ctx1 M ctx w c.
    generalize dependent e2.
    induction M2; intros; inversion I2; subst.
    - apply productive_complete.
      exists we. assumption.
    - apply IHM2. assumption.
  + repeat rewrite Bool.orb_true_iff.
    right. left.
    destruct we.
    { contradiction. }
    apply has_first_complete.
    exists c0, we. assumption.
Qed.

Theorem has_first_zipper_complete_unfocus :
  forall z,
    (exists c w, matches (unfocus z) (c :: w)) ->
    has_first_zipper z = true.
Proof.
  intros z [c [w M]].
  rewrite <- unfocus_correct in M.
  apply has_first_zipper_complete.
  exists c, w. assumption.
Qed.

(** Extraction *)

(* Tell Coq to extract Coq's [bool], [list] & [char] types 
   to their OCaml counterparts *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant char => "char".
Extraction "edelmann.ml" accepts.  