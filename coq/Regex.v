Require Export List Bool Ascii String Arith Lia Nat.
Export ListNotations BoolNotations.
From stdpp Require Export gmap sets fin_sets.
Open Scope list_scope.

Ltac simp tac :=
  repeat match goal with
  | |- ?x = ?x => reflexivity
  | H : ?x = ?x |- _ => clear H
  | |- forall _, _ => intro
  | |- _ -> _ => intro
  | H : False |- _ => destruct H
  | H : True |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : _ <-> _ |- _ => destruct H
  | x : _ * _ |- _ => destruct x
  | H1 : ?P -> ?Q, H2 : ?P |- _ => specialize (H1 H2)
  | H : True -> ?Q |- _ => specialize (H I)
  | |- _ => progress (simplify_eq; auto)
  | |- _ => progress set_unfold
  | |- _ => progress unfold orb, andb in *
  (* Do tactics that create multiple subgoals last *)
  | |- _ /\ _ => split
  | |- _ <-> _ => split
  | H : _ \/ _ |- _ => destruct H
  | |- _ => case_decide
  | [ H: ?x ++ ?y = [] |- _ ] => destruct x, y
  | [ H: [] = ?x ++ ?y |- _ ] => destruct x, y
  | [ H: context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?
  | [ H: context[if ?b then _ else _] |- _ ] => destruct b eqn:?
  | [ |- context[if ?b then _ else _] ] => destruct b eqn:?
  | |- _ \/ _ => solve [left; simp tac | right; simp tac]
  | |- _ => lia
  | |- _ => congruence
  | |- _ => progress tac
  end.

Definition char := ascii.
Definition string := list ascii.

Definition char_dec := ascii_dec.

(* Regular expressions *)
Inductive re :=
  | Void : re
  | Epsilon : re
  | Atom : char -> re
  | Union : re -> re -> re
  | Concat : re -> re -> re
  | Star : re -> re.

(* Matching relation *)
Inductive matches : re -> string -> Prop :=
  | matches_isEpsilon : matches Epsilon []
  | matches_atom a : matches (Atom a) [a]
  | matches_union_l r1 r2 s :
      matches r1 s -> 
      matches (Union r1 r2) s
  | matches_union_r r1 r2 s :
      matches r2 s -> 
      matches (Union r1 r2) s
  | matches_concat r1 r2 s1 s2 s3 : 
      matches r1 s1 -> 
      matches r2 s2 ->
      s3 = s1 ++ s2 -> 
      matches (Concat r1 r2) s3
  | matches_star_empty r : 
      matches (Star r) []
  | matches_star_step r s1 s2 s3 : 
      matches r s1 -> 
      matches (Star r) s2 -> 
      s3 = s1 ++ s2 -> 
      matches (Star r) s3.

Hint Constructors matches : core.

(* A lemma relating cons and [++] *)
Lemma cons_eq_app {A} (a : A) x y z : 
  a :: x = y ++ z -> (y = [] /\ z = a :: x) \/ 
  (exists y', y = a :: y' /\ x = y' ++ z).
Proof.
  intros H. replace (a :: x) with ([a] ++ x) in H; last done.
  apply app_eq_app in H. simp eauto. destruct y; simp eauto.
Qed.

(* Inversion lemma for [Star] *)
Lemma star_inv r s : 
  s ≠ [] -> matches (Star r) s -> 
  exists (s1 s2 : string), s1 ≠ [] /\ s = s1 ++ s2 
  /\ matches r s1 /\ matches (Star r) s2.
Proof.
  intros Hs Hr. remember (Star r). 
  revert r Heqr0. induction Hr; simp eauto.
  destruct s1; simp eauto. 
  exists (a :: s1). simp eauto.
Qed.

Ltac inv' H := inversion H; clear H; simplify_eq.
Ltac auto_inv :=
  try match goal with
  | [ H : matches Void _ |- _ ] => inv' H
  | [ H : matches (Epsilon) _ |- _ ] => inv' H
  | [ H : matches (Atom _) _ |- _ ] => inv' H
  | [ H : matches (Union _ _) _ |- _ ] => inv' H
  | [ H : matches (Concat _ _) _ |- _ ] => inv' H
  | [ H : matches (Star _) (_ :: _) |- _ ] => apply star_inv in H
  | [ H : _ :: _ = ?x ++ ?y |- _ ] => apply cons_eq_app in H
  end; eauto.
Ltac X := simp auto_inv.

(** True if the regular expression matches the empty string *)
Fixpoint isEmpty (r : re) : bool :=
  match r with
  | Void => false
  | Epsilon => true
  | Atom _ => false
  | Union r1 r2 => isEmpty r1 || isEmpty r2
  | Concat r1 r2 => isEmpty r1 && isEmpty r2
  | Star _ => true
  end.

Lemma isEmpty_matches_1 r : isEmpty r = true -> matches r [].
Proof. induction r; X. Qed.

Lemma isEmpty_matches_2 r : matches r [] -> isEmpty r = true.
Proof. remember []. induction 1; X. Qed.

Hint Resolve isEmpty_matches_1 isEmpty_matches_2 : core.

(******************************************************************************)
(* Our code below *)

(* Checks if this is a regex that never matches any string *)
Fixpoint isVoid (r : re) : bool :=
  match r with 
  | Void => true 
  | Concat r1 r2 => isVoid r1 || isVoid r2 
  | Union r1 r2 => isVoid r1 && isVoid r2 
  | Star _ => false  (* Star can always match the empty string *)
  | Atom _ => false 
  | Epsilon => false 
  end.

Lemma re_dec : forall r1 r2 : re, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. apply char_dec. Qed.

Instance ReDecidable : EqDecision re := re_dec.
