Require Import List.
Import ListNotations.
From stdpp Require Import gmap.

(* Custom Ltac to simplify goals *)
Ltac simp tac :=
  repeat match goal with
  | |- ?x = ?x => reflexivity
  | H : ?x = ?x |- _ => clear H
  | |- ∀ _, _ => intro
  | |- _ -> _ => intro
  | H : False |- _ => destruct H
  | H : True |- _ => destruct H
  | H : ∃ _, _ |- _ => destruct H
  | H : _ ∧ _ |- _ => destruct H
  | H : _ ↔ _ |- _ => destruct H
  | x : _ * _ |- _ => destruct x
  | H1 : ?P -> ?Q, H2 : ?P |- _ => specialize (H1 H2)
  | H : True -> ?Q |- _ => specialize (H I)
  | |- _ => progress (simplify_eq; auto)
  | |- _ => progress set_unfold
  | |- _ => progress unfold orb, andb in *
  (* Do tactics that create multiple subgoals last *)
  | |- _ ∧ _ => split
  | |- _ ↔ _ => split
  | H : _ ∨ _ |- _ => destruct H
  | |- _ => case_decide
  | [ H: ?x ++ ?y = [] |- _ ] => destruct x, y
  | [ H: [] = ?x ++ ?y |- _ ] => destruct x, y
  | [ H: context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?
  | [ H: context[if ?b then _ else _] |- _ ] => destruct b eqn:?
  | [ |- context[if ?b then _ else _] ] => destruct b eqn:?
  | |- _ ∨ _ => solve [left; simp tac | right; simp tac]
  | |- _ => lia
  | |- _ => congruence
  | |- _ => progress tac
  end.

Parameter T : Type.
Parameter eq_dec : forall x y : T, {x = y} + {x <> y}.

(* Regular expressions *)

Inductive re : Type :=
  | Empty : re
  | Epsilon : re
  | Atom : T -> re
  | Union : re -> re -> re
  | Concat : re -> re -> re
  | Star : re -> re.

(* Matching relation *)
Inductive matches : re -> list T -> Prop :=
  | matches_epsilon : matches Epsilon []
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

(* A lemma relating cons and [++] *)
Lemma cons_eq_app {A} (a : A) x y z : 
  a :: x = y ++ z -> (y = [] ∧ z = a :: x) ∨ (∃ y', y = a :: y' ∧ x = y' ++ z).
Proof.
  intros H. replace (a :: x) with ([a] ++ x) in H; last done.
  apply app_eq_app in H. simp eauto. destruct y; simp eauto.
Qed.

(* Inversion lemma for [Star] *)
Lemma star_inv r s : 
  s ≠ [] -> 
  matches (Star r) s -> 
  ∃ s1 s2, s1 ≠ [] ∧ s = s1 ++ s2 ∧ matches r s1 ∧ matches (Star r) s2.
Proof.
  intros Hs Hr. remember (Star r). revert r Heqr0. induction Hr; simp eauto.
  destruct s1; simp eauto. exists (t :: s1). simp eauto.
Qed.

Ltac inv H := inversion H; clear H; simplify_eq.
Ltac auto_inv :=
  try match goal with
  | [ H : matches Empty _ |- _ ] => inv H
  | [ H : matches (Epsilon) _ |- _ ] => inv H
  | [ H : matches (Atom _) _ |- _ ] => inv H
  | [ H : matches (Union _ _) _ |- _ ] => inv H
  | [ H : matches (Concat _ _) _ |- _ ] => inv H
  | [ H : matches (Star _) (_ :: _) |- _ ] => apply star_inv in H
  | [ H : _ :: _ = ?x ++ ?y |- _ ] => apply cons_eq_app in H
  end; eauto.

Ltac X := simp auto_inv.

(* Add constructors of matches to the core auto database *)
Hint Constructors matches : core.

(* Regular expression matching with derivatives *)

(* True if the regular expression matches the empty string *)
Fixpoint eps (r : re) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Atom _ => false
  | Union r1 r2 => eps r1 || eps r2
  | Concat r1 r2 => eps r1 && eps r2
  | Star _ => true
  end.

Lemma eps_matches_1 r : eps r = true -> matches r [].
Proof. induction r; X. Qed.

Lemma eps_matches_2 r : matches r [] -> eps r = true.
Proof. remember []. induction 1; X. Qed.

Hint Resolve eps_matches_1 eps_matches_2 : core.

(* Derivative of a regular expression with respect to a character *)
Fixpoint der (r : re) (a : T) : re :=
  match r with
  | Empty => Empty
  | Epsilon => Empty
  | Atom b => if eq_dec a b then Epsilon else Empty
  | Union r1 r2 => Union (der r1 a) (der r2 a)
  | Concat r1 r2 => 
    if eps r1 
      then Union (Concat (der r1 a) r2) (der r2 a) 
    else Concat (der r1 a) r2
  | Star r => Concat (der r a) (Star r)
  end.

Lemma der_matches_1 a r s : matches (der r a) s -> matches r (a :: s).
Proof. revert s. induction r; X. Qed.

Lemma der_matches_2 a r s : matches r (a :: s) -> matches (der r a) s.
Proof. revert s. induction r; X. apply eps_matches_2 in H2. X. Qed.

Hint Resolve der_matches_1 der_matches_2 : core.

Definition matches' (r : re) (s : list T) : bool :=
  eps (fold_left der s r).

Lemma matches'_matches r s : matches' r s = true <-> matches r s.
Proof. unfold matches'. split; revert r; induction s; X. Qed.

(* From Jules:

  This could be extended in various ways:
  - Other logical operators (negation, intersection, xor)
  - Weighted version
  - Antimirov derivatives
  - Apply simplification rules to regexes, prove that derivatives only 
    generate finitely many regexes up to the simplification rules 
    (so that you could build a DFA with it)

*)
