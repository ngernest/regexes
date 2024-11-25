Require Export Regex.
Require Export Lia.

(** If r is a regex and a is a char, then a partial derivative
    is a regex r' such that if r' accepts word s, then r accepts a ⋅ s.
    We can construct sets of partial derivatives (Antimirov derivatives) *)

(* Note that gsets are finite *)
Fixpoint a_der (r : re) (c : char) : gset re :=
  match r with
  | Void => ∅
  | Epsilon => ∅
  | Atom b => if char_dec c b then {[ Epsilon ]} else ∅
  | Union r1 r2 => (a_der r1 c) ∪ (a_der r2 c)
  | Concat r1 r2 => 
    if isEmpty r1 
      then (set_map (fun r => Concat r r2) (a_der r1 c)) ∪ (a_der r2 c) 
    else (set_map (fun r => Concat r r2) (a_der r1 c))
  | Star r => set_map (fun r' => Concat r' (Star r)) (a_der r c)
  end.

(** Takes the Antimirov derivative wrt a string *)
Fixpoint a_der_str (r : re) (s : string) : gset re :=
  match s with
  | [] => {[ r ]}
  | (c :: cs) => set_bind (fun r' => a_der_str r' cs) (a_der r c)
  end.

(** Applies Antimirov point-wise to each regex in [rs] 
    - [set_bind] is like [concatMap] for the list monad but using 
      set union instead *)
Definition a_der_set (rs : gset re) (c : char) : gset re :=
  set_bind (fun r => a_der r c) rs.
  
(** Lemmas about a_der_set *)
Lemma a_der_set_singleton (r : re) (c : char) : 
  a_der_set {[ r ]} c = a_der r c.
Proof. set_solver. Qed. 
Hint Rewrite a_der_set_singleton : core.

Lemma a_der_set_empty (c : char) : a_der_set ∅ c = ∅.
Proof. set_solver. Qed.
Hint Rewrite a_der_set_empty : core.

Lemma a_der_set_union (c : char) (s1 s2 : gset re) : 
  a_der_set (s1 ∪ s2) c = a_der_set s1 c ∪ a_der_set s2 c.
Proof. set_solver. Qed.
Hint Rewrite a_der_set_union : core. 

Lemma a_der_set_Union (c : char) (r1 r2 : re) : 
  a_der_set {[ Union r1 r2 ]} c = a_der_set {[ r1 ]} c ∪ a_der_set {[ r2 ]} c.
Proof. rewrite ! a_der_set_singleton. simpl. reflexivity. Qed.

Lemma a_der_set_eps (c : char) : a_der_set {[ Epsilon ]} c = ∅.
Proof. rewrite a_der_set_singleton. reflexivity. Qed. 
Hint Rewrite a_der_set_eps : core.

Lemma a_der_set_atom (c : char) : a_der_set {[ Atom c ]} c = {[ Epsilon ]}.
Proof. 
  rewrite a_der_set_singleton. simpl. destruct char_dec. 
  reflexivity. contradiction. 
Qed.

Lemma a_der_set_atom' (c a : char) : a ≠ c -> 
  a_der_set {[ Atom c ]} a = ∅.
Proof. 
  rewrite a_der_set_singleton. simpl. destruct char_dec. 
  intros. contradiction. reflexivity. 
Qed.

(** Matching principles for a_der *)
(** True if there is a regex in the set which matches the empty string *)
Definition nullable (rs : gset re) : bool :=
  let elem_of_bool (x : bool) (s : gset bool) := bool_decide (x ∈ s) in
  elem_of_bool true (set_map (fun r => isEmpty r) rs).

(** True if r matches s, using a_der_set *)
Definition a_matches (r : re) (s : string) : bool :=
  nullable (fold_left a_der_set s {[ r ]}).

(** Alternate definition using a_der_str *)
Definition a_matches' (r : re) (s : string) : bool :=
  nullable (a_der_str r s).

(** Lemmas about fold_left a_der_set *)
Lemma fold_left_empty (s : string) : fold_left a_der_set s ∅ = ∅.
Proof. induction s; autorewrite with core; eauto. Qed.
Hint Rewrite fold_left_empty : core. 

Lemma fold_left_union (s : string) (s1 s2 : gset re) : 
  fold_left a_der_set s (s1 ∪ s2) = fold_left a_der_set s s1 ∪ fold_left a_der_set s s2. 
Proof. 
  revert s1 s2. induction s; intros; simpl; eauto; 
  autorewrite with core; apply IHs. 
Qed.
Hint Rewrite fold_left_union : core.

(** Lemmas about set_bind *)
Lemma set_bind_empty (f : re -> gset re) : set_bind f (∅ : gset re) = ∅.
Proof. set_solver. Qed.
Hint Rewrite set_bind_empty : core.

Lemma set_bind_singleton (f : re -> gset re) (r : re) : 
  set_bind f ({[ r ]} : gset re) = f r.
Proof. set_solver. Qed.
Hint Rewrite set_bind_singleton : core.

Lemma set_bind_union (f : re -> gset re) (r1 r2 : gset re) :
  set_bind f (r1 ∪ r2) = set_bind f r1 ∪ set_bind f r2.
Proof. set_solver. Qed. 
Hint Rewrite set_bind_union : core. 

Lemma set_bind_id (rs : gset re) : 
  set_bind (λ r, {[ r ]}) rs = rs.
Proof. set_solver. Qed.
Hint Rewrite set_bind_id : core.

Lemma a_matches_matches'_help : forall (s : string) (rs : gset re), 
  fold_left a_der_set s rs =
  set_bind (fun r => a_der_str r s) rs.
Proof.
  induction s. 
  - simpl. intros. set_solver.
  - intros. simpl. rewrite IHs. unfold a_der_set.
    set_solver.
Qed.

(** The two a_matches definitions are equivalent *)
Theorem a_matches_matches' (r : re) (s : string) : 
  a_matches r s <-> a_matches' r s.
Proof.
  unfold a_matches, a_matches'.
  cut (fold_left a_der_set s {[ r ]} = a_der_str r s).
  { intros. rewrite H. reflexivity. }
  rewrite a_matches_matches'_help. 
  rewrite set_bind_singleton. reflexivity.
Qed.

(** What it means for a string to match a set of regexes.
    - [matches_set_here]: if [s] matches [r], then [s] matches any regex set 
      containing [r] 
    - [matches_set_there]: if [s] matches a regex set [rs], 
      then [s] matches the union of [rs] with any other singleton regex set *)
Inductive matches_set : string -> gset re -> Prop :=
  | matches_set_here (r : re) (s : string) (rs : gset re) : 
      matches r s -> r ∈ rs -> 
      matches_set s rs
  | matches_set_there (r : re) (s : string) (rs : gset re) : 
      matches_set s rs -> 
      matches_set s ({[ r ]} ∪ rs).

(** An alternate formulation of [matches_set] *)
Definition matches_set' (s : string) (rs : gset re) :=
  ∃ r, r ∈ rs /\ matches r s.      

(** Proving that the two statements of [matches_set] are equivalent *)
Lemma matches_set_matches_set' : forall (s : string) (rs : gset re),
  matches_set s rs <-> matches_set' s rs.
Proof.
  split; intros.
  - induction H. unfold matches_set'. 
    exists r. split; try assumption. set_solver.
  - induction H. destruct H as [H1 H2].
    eapply matches_set_here; eauto.
Qed.    
    
(** Some lemmas about [matches_set], adapted from the Agda proofs in 
    https://monog.ufop.br/server/api/core/bitstreams/d7d18cf6-ff09-4b32-99a6-d87235f7a3ce/content *)

(** If [s] matches the regex set [rs], then [s] matches [rs ∪ rs'] 
    for any other set [rs']. *)
Lemma matches_set_weakening_left : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> matches_set s (rs ∪ rs').
Proof.
  intros. induction H.
  - eapply matches_set_here. apply H. 
    apply elem_of_union_l. assumption.
  - replace ({[r]} ∪ rs ∪ rs') with ({[r]} ∪ (rs ∪ rs')) by set_solver.
    eapply matches_set_there. assumption.
Qed.

(** If [s] matches the regex set [rs], then [s] matches [rs' ∪ rs] 
    for any other set [rs']. *)
Lemma matches_set_weakening_right : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> matches_set s (rs' ∪ rs).
Proof.
  intros. induction H.
  - eapply matches_set_here. apply H. 
    apply elem_of_union_r. assumption.
  - replace (rs' ∪ ({[r]} ∪ rs)) with ({[r]} ∪ (rs' ∪ rs)) by set_solver.
    eapply matches_set_there. assumption.
Qed.    

(** An inversion lemma for [Union] using [matches_set'] *)    
Lemma matches_set_union_inv : forall (rs1 rs2 : gset re) (s : string),
  matches_set' s (rs1 ∪ rs2) -> matches_set' s rs1 \/ matches_set' s rs2.
Proof.
  intros. induction H. destruct H as [H1 H2].
  set_unfold. set_solver.
Qed.  

(** No string matches the empty regex set *)
Lemma not_matches_empty (s : string) : ~(matches_set s ∅).
Proof.
  unfold not. intros.
  inversion H; subst; set_solver.
Qed.

(** If [s] matches [r], then [s] matches the singleton set containing [r] *)
Lemma matches_singleton' (s : string) (r : re) : 
  matches r s -> matches_set s {[ r ]}.
Proof. intros; eapply matches_set_here; eauto; set_solver. Qed.  

(** The empty string matches the singleton set containing [Epsilon] *)
Lemma matches_set_epsilon : matches_set [] {[Epsilon]}.
Proof. eapply matches_set_here. apply matches_epsilon. set_solver. Qed.

Lemma a_der_matches_1 a r s : matches_set' s (a_der r a) -> matches r (a :: s).
Proof. 
  revert s.
  induction r; X; try (apply not_matches_empty in H; destruct H).
  eapply matches_concat.
  apply isEmpty_matches_1 in Heqb.
  apply Heqb. apply IHr2.
  eexists. split.
  - apply H.
  - apply H0.
  - simpl. reflexivity.
Qed.

Lemma a_der_matches_2 a r s : matches r (a :: s) -> matches_set' s (a_der r a).
Proof.
  revert s. induction r; X.
  - specialize IHr1 with s. 
    apply IHr1 in H3.
    destruct H3 as [x [H1 H2]].
    exists x. split.
    + left. assumption.
    + assumption.
  - specialize IHr2 with s.
    apply IHr2 in H3.
    destruct H3 as [x [H1 H2]].
    exists x. split.
    + right. assumption.
    + assumption.
  - specialize IHr2 with s.
    apply IHr2 in H3.
    destruct H3 as [x [H3 H4]].
    exists x. split. 
    + right. assumption.
    + assumption.
  - specialize IHr1 with x.
    apply IHr1 in H2.
    destruct H2 as [x0 [H4 H5]].
    exists (Concat x0 r2). split. left.
    exists x0. split.
    + reflexivity.
    + assumption.
    + eapply matches_concat; eauto.
  - apply isEmpty_matches_2 in H2. rewrite H2 in Heqb. discriminate Heqb.
  - specialize IHr1 with x. apply IHr1 in H2. 
    destruct H2 as [x0 [H4 H5]].
    exists (Concat x0 r2). split.
    exists x0. split; eauto.
    eapply matches_concat; eauto.
  - fold a_der. specialize IHr with x1.
    apply IHr in H1.
    destruct H1 as [x [H3 H4]].
    eexists. split.
    exists x. split; eauto.
    eapply matches_concat; eauto.
Qed.    
