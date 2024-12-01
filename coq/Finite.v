Require Import Regex.
Require Import Antimirov. 
Require Import Brzozowski.

(** Proving that taking the Antimirov derivative wrt a word will always
    generate a finite set *)

(* Crashes Coq *)
(* Definition a := ascii_of_nat 1.
Definition b := ascii_of_nat 2.
Compute (a_der_str (Union (Atom a) (Atom b)) [a]). *)

(** Generates the (overestimated) set containing all possible Antimirov derivatives of r, 
    with respect to any word *)
Fixpoint A_der (r : re) : gset re :=
  match r with
  | Void => {[ Void ]}
  | Epsilon => {[ Epsilon ]}
  | Atom b => {[ Epsilon; Atom b ]}
  | Union r1 r2 => (A_der r1) ∪ (A_der r2) ∪ {[ Union r1 r2 ]}
  | Concat r1 r2 => (A_der r2) ∪ (set_map (fun r' => Concat r' r2) (A_der r1))
  | Star r => (set_map (fun r' => Concat r' (Star r)) (A_der r))
    ∪ {[ Star r ]}
  end.

Lemma re_in_A_der : forall (r : re), r ∈ A_der r.
Proof. induction r; simpl; set_solver. Qed.

(** Let r be a regex. We know that A_der r is finite.
    With this lemma, we show that the set of Antimirov derivatives of r 
    with respect to any nonempty word is finite. 
    i.e. {a_der r w | w ∈ Σ+} is finite *)
Lemma a_finite_char (r : re) : forall (a : re), a ∈ A_der r -> 
  forall (c : char), a_der a c ⊆ A_der r.
Proof. 
  induction r; X; fold A_der a_der in *.
  - left. left. eapply IHr1. apply re_in_A_der. apply H. 
  - left. right. eapply IHr2. apply re_in_A_der. apply H.
  - left. eapply IHr2. apply re_in_A_der. apply H.
  - left. exists x1. split. reflexivity. 
    eapply IHr. apply re_in_A_der. apply H0.
  - left. exists x0. split. reflexivity.
    eapply IHr. apply re_in_A_der. apply H0.
Qed.

Lemma set_bind_subset : forall (f : re -> gset re) (s s' : gset re),
  s ⊆ s' -> (forall r, r ∈ s -> f r ⊆ s') -> set_bind f s ⊆ s'.
Proof. set_solver. Qed.

Lemma A_der_subset : forall (r r0 : re) (a : char), 
    r0 ∈ a_der r a -> A_der r0 ⊆ A_der r.
Proof. induction r; X. Qed.

Lemma subset_trans (A B C : gset re) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. set_solver. Qed.

(** Antimirov derivative wrt a string is finite *)
Theorem a_finite : forall (s : string) (r : re), a_der_str r s ⊆ A_der r.
Proof. induction s; intros; simpl.
  - cut (r ∈ A_der r). set_solver. apply re_in_A_der.
  - apply set_bind_subset. apply a_finite_char. 
    apply re_in_A_der. intros. 
    eapply subset_trans. apply IHs. eapply A_der_subset. apply H. 
Qed.

Definition all_chars : gset char := 
  list_to_set (map Ascii.ascii_of_nat (seq 0 128)).

Lemma char_in_all : forall (c : char), c ∈ all_chars.
Proof. Admitted.

(** Generates all possible Brzozowski derivatives wrt any string *)
(* Fixpoint B_der (r : re) : gset re :=
  match r with
  | Void => {[ Void ]}
  | Epsilon => {[ Void; Epsilon ]}
  | Atom b => {[ Void; Epsilon; Atom b ]}
  | Union r1 r2 => 
    set_map (fun '(r1', r2') => Union r1' r2') (cprod (B_der r1) (B_der r2))
  | Concat r1 r2 => (set_map (fun '(r1', r2') => Union r1' r2')
      (cprod (set_map (fun r' => Concat r' r2 : re) (B_der r1) : gset re) 
      (B_der r2))) 
      ∪ (set_map (fun r' => Concat r' r2) (B_der r1) : gset re)
  | Star r => (set_bind (fun r' => B_der (Concat r' (Star r))) (B_der r)) ∪ {[ Star r ]}
  end. *)

(* Definition B_der (r : re) : gset re :=  {fold sum a | a ⊂ A(r)}. *)
