Require Export List Bool Ascii String Arith Lia Nat.
Export ListNotations BoolNotations.
Require Import Regex.

(******************************************************************************)

(* Comparison function (<=) for regular expressions *)
Fixpoint re_le (r1 r2 : re) : bool :=
  match r1, r2 with
  | Void, Void 
  | Void, _ => true
  | Epsilon, Void => false
  | Epsilon, Epsilon 
  | Epsilon, _ => true
  | Atom _, Void 
  | Atom _, Epsilon => false
  | Atom c1, Atom c2 => (nat_of_ascii c1) <=? (nat_of_ascii c2)
  | Atom _, _ => true
  | Union _ _, Void 
  | Union _ _, Epsilon 
  | Union _ _, Atom _ => false
  | Union r11 r12, Union r21 r22 => re_le r11 r21 && re_le r12 r22
  | Union _ _, _ => true
  | Concat _ _, Void
  | Concat _ _, Epsilon 
  | Concat _ _, Atom _ 
  | Concat _ _, Union _ _ => false
  | Concat r11 r12, Concat r21 r22 => re_le r11 r21 && re_le r12 r22
  | Concat _ _, _ => true
  | Star r1', Star r2' => re_le r1' r2'
  | Star _, _ => false  
  end.

(* <= for regexes is reflexive *)
Lemma re_le_refl : forall (r : re),
  re_le r r = true.
Proof.
  induction r; auto;
  try (simpl; rewrite IHr1; rewrite IHr2; auto).
  - (* Atom *)
    simpl. remember (nat_of_ascii c) as n. 
    rewrite leb_correct. 
    + reflexivity. 
    + lia.
Qed.    

(******************************************************************************)
(** Smart constructors for regexes *)

Fixpoint merge_re (r : re) : re -> re :=
  match r with 
  | Union r1 r2 => 
    (fix inner_merge (r' : re) : re :=
      match r' with 
      | Union r1' r2' => 
        if re_le r1 r1' then 
          Union r1 (merge_re r2 r')
        else 
          Union r2 (inner_merge r2')
      | _ => Union r1 r2 
      end)
  | _ => fun r' => r'
  end.

Definition re_to_list (r : re) : list re :=
  match r with 
  | Union r1 r2 => [r1; r2]
  | _ => [r]
  end.

Require Import Coq.Program.Wf.

Lemma length_cons {A : Type} : forall (x : A) (xs : list A),
  length (x :: xs) = 1 + length xs.
Proof.
  intros. destruct xs; simpl; reflexivity.
Qed.


Program Fixpoint merge_re' (xs ys : list re) 
  { measure (length xs + length ys) } : list re :=
  match xs, ys with 
  | [], _ => ys 
  | _, [] => xs 
  | x::xs', y::ys' =>
    if re_le x y then 
      x :: (merge_re' xs' ys)
    else 
      y :: (merge_re' xs ys')
  end.
Next Obligation.
  intros. subst.  
  repeat (rewrite length_cons). lia.
Defined.   
Next Obligation. 
  intros. subst.  
  repeat (rewrite length_cons). lia.
Defined.   
Next Obligation. 
  simpl. intros. unfold not. 
  intros.
  destruct H. discriminate H.
Defined.
Next Obligation.
  Admitted. (* not sure how to satisfy this proof obligation involving [Acc] *)
  

(** Smart constructor for [Union] 
    - TODO: figure out how to satisfy the termination checker
      (reference the stuff involving measures in lecture 7)
*)
Fail Fixpoint union (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (_, Void) => r1 
  | (Void, _) => r2 
  | (Union r11 r12, _) => union r11 (union r12 r2)
  | (a, Union b c) => 
    if negb (re_le a b) then 
      union b (union a c)
    else 
      Union r1 r2
  | (_, _) => 
    if negb (re_le r1 r2) then union r2 r1 
    else Union r1 r2 
  end.

(** Smart constructor for [Concat] *)
Definition concat (r1 : re) (r2 : re) : re :=
  match (r1, r2) with 
  | (Void, _) => Void 
  | (_, Void) => Void 
  | (Epsilon, _) => r2 
  | (_, Epsilon) => r1 
  | (_, _) => Concat r1 r2 
  end.

(** Smart constructor for [Star]. Note:
    - Iterating the empty string gives us the empty string
    - Zero or more occurrences of Void is empty
    - Two iterations of [Star] is the same as one *)
Definition star (r : re) := 
  if isEmpty r || isVoid r then Epsilon 
  else match r with 
  | Star r' => Star r' 
  | _ => Star r
  end.

Definition star' (r : re) := 
  match r with 
  | Epsilon | Void => Epsilon 
  | Star r' => Star r' 
  | _ => Star r
  end.  



(* If [s] matches [r], then [s] also matches [Star r]. 
   - Adapted from the [IndProp] chapter of Software Foundations *)
Lemma star_1 : forall (r : re) (s : string),
  matches r s -> 
  matches (Star r) s.
Proof.
  intros.
  rewrite <- app_nil_r.
  eapply matches_star_step; auto.
  apply H.
Qed.  

(* Inversion lemma for atoms *)
Lemma atom_inv : forall r a,
  matches r [a] -> r = Atom a.
Proof.
  intros.
  induction r; inversion H; eauto.
  - subst. apply IHr1 in H3. subst.
Admitted. (* TODO *)
     

Lemma star_app : forall (s1 s2 : string) (r : re),
  matches (Star r) s1 -> 
  matches (Star r) s2 -> 
  matches (Star r) (s1 ++ s2).
Proof.
  intros s1 s2 r H1.
  remember (Star r) as r'.
  revert s2.
  induction H1; try discriminate.
  - (* matches_star_empty *)
    intros. simpl. assumption.
  - (* matches_star_step *)
    X. apply IHmatches2 in H0.
    rewrite <- app_assoc. 
    eapply matches_star_step.
    + apply H1_.
    + apply H1_0.
    + admit.  
Admitted. (* TODO *)    
  
  

Lemma star'_sound : forall (r : re) (s : string),
  matches (Star r) s <-> matches (star' r) s.
Proof.
  intros r. split; intros H.
  - (* -> *)
    induction H; X.
    induction r; X.
    + admit. 
    + admit. 
    + remember (star' r) as r'.
      apply isEmpty_matches_1. 
      subst. destruct r; simpl; X.
    + simpl.
Admitted. (* TODO *)
    
  

Lemma star_smart_constructor_sound : forall (r : re) (s : string),
  matches (Star r) s <-> matches (star r) s.
Proof.
  intros r. split; intros H.
  - (* -> *)  
    induction H; X.
    induction r; X.
    + (* Union *)
      unfold star. 
      remember (Union r1 r2) as r'.
      destruct (isEmpty r') eqn:E1; simpl; eauto.
      destruct (isVoid r') eqn:E2; simpl; eauto.
    + (* Concat *)
      unfold star.
      remember (Concat r1 r2) as r'.
      destruct (isEmpty r') eqn:E1; simpl; eauto.
      destruct (isVoid r') eqn:E2; simpl; eauto.
    + (* Atom *)    
      admit. 
Admitted. (* TODO *)
      

    

(** Returns [Epsilon] if [r] matches the empty string, 
    otherwise matches [Void] *)
Definition E (r : re) : re :=
  if isEmpty r then Epsilon else Void.

(** Helper function for standardizing regexes: computes L(r) ∖ {∊}
    - TODO: figure out why this works *)
Fixpoint N (r : re) : re :=
  match r with 
  | Void => Void 
  | Epsilon => Epsilon 
  | Atom c => Atom c 
  | Union r1 r2 => Union (N r1) (N r2)
  | Concat r1 r2 => 
    Union 
      (Union (Concat (E r1) (N r2)) (Concat (N r1) (E r2)))
      (Concat (N r1) (N r2))
  | Star r' => Concat (N r') (star (N r'))
  end.
