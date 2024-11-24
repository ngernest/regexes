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

(* Lemma blah : forall (x1 x2 r1 r2 : re) (c : char), 
  x1 ∈ a_der r1 c -> x2 ∈ a_der r2 c -> 
  (Concat x1 x2) ∈ a_der (Concat r1 r2) c.
Proof. intros. simpl. destruct isEmpty.
  - apply elem_of_union_l. 
Admitted. *)

(* Lemma blah2 : forall (x1 x2 r1 r2 : re) (s : string), 
  x1 ∈ fold_left a_der_set s {[r1]} -> x2 ∈ fold_left a_der_set s {[r2]} -> 
  (Concat x1 x2) ∈ a_der_str (Concat r1 r2) s.
Proof. intros. destruct s.
  - simpl in *. 
Admitted. *)

(* Lemma blah3 : forall (r : re) (a : char) (s : string),
 fold_left a_der_set s (a_der r a) = a_der_str r (a :: s).
Proof. Admitted. *)

Fixpoint concat_str (s : string) (r : re) :=
  match s with 
  | [] => r
  | (c :: cs) => Concat (Atom c) (concat_str cs r)
  end.

(* Lemma a_matches_matches' (r : re) (s : string) : 
  a_matches r s <-> a_matches' r s.
Proof. 
  induction s.
  - unfold a_matches, a_matches', nullable. X.
  - unfold a_matches, a_matches', nullable in *. X. 
    + destruct H5. 
Admitted. *)

(* Lemma a_matches_matches'' (r : re) (s : string) : 
  a_matches r s <-> a_matches' r s.
Proof. 
  induction r; unfold a_matches, a_matches', nullable in *. 
  - X; destruct H1; destruct s; simpl in *;
    autorewrite with core in *; eauto. 
  - X; destruct H1; destruct s; simpl in *;
    autorewrite with core in *; eauto. 
  - X; destruct H1; exists x; split; destruct s; eauto; simpl in *;
    destruct char_dec; autorewrite with core in *; simpl in *;
    destruct char_dec; destruct s; simpl in *; autorewrite with core in *; 
    eauto; contradiction. 
  - X; destruct H9; exists x; split; eauto; destruct s; eauto; simpl in *; 
    autorewrite with core in *; simpl in *; autorewrite with core in *. 
    + apply elem_of_union in H4. destruct H4.
      * apply elem_of_union_l. induction s; simpl in *; eauto. 
        -- rewrite set_bind_id. apply H4.
        -- admit.
      * apply elem_of_union_r. induction s; simpl in *; eauto.
        -- rewrite set_bind_id. apply H4.
        -- admit.
    + admit.
    + admit. 
    + admit.
    + admit. 
    + admit. 
    + admit. 
    + admit. 
  - X; destruct H9. exists (Concat x3 x1). split.
    + simpl. rewrite <- H2, H0. rewrite andb_diag. reflexivity. 
    + apply blah2. apply H8. apply H6. 
Admitted. *)

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

(* An alternate formulation of [matches_set] *)
Definition matches_set' (s : string) (rs : gset re) :=
  ∃ r, r ∈ rs /\ matches r s.      

(* Some lemmas about [matches_set], adapted from the Agda proofs in 
   Adapted from https://monog.ufop.br/server/api/core/bitstreams/d7d18cf6-ff09-4b32-99a6-d87235f7a3ce/content *)

(* If [s] matches the regex set [rs], then [s] matches [rs ∪ rs'] 
  for any other set [rs']. *)
Lemma matches_set_weakening_left : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> matches_set s (rs ∪ rs').
Proof.
  intros. induction H.
  - (* matches_set_here *)  
    eapply matches_set_here. apply H. 
    apply elem_of_union_l. assumption.
  - (* matches_set_there *)
    replace ({[r]} ∪ rs ∪ rs') with ({[r]} ∪ (rs ∪ rs')) by set_solver.
    eapply matches_set_there.
    assumption.
Qed.

(* If [s] matches the regex set [rs], then [s] matches [rs' ∪ rs] 
  for any other set [rs']. *)
Lemma matches_set_weakening_right : forall (rs rs' : gset re) (s : string),
  matches_set s rs -> matches_set s (rs' ∪ rs).
Proof.
  intros. induction H.
  - (* matches_set_here *)  
    eapply matches_set_here. apply H. 
    apply elem_of_union_r. assumption.
  - (* matches_set_there *)
    replace (rs' ∪ ({[r]} ∪ rs)) with ({[r]} ∪ (rs' ∪ rs)) by set_solver.
    eapply matches_set_there.
    assumption.
Qed.    

(* An inversion lemma for [Union] using [matches_set'] *)    
Lemma matches_set_union_inv : forall (rs1 rs2 : gset re) (s : string),
  matches_set' s (rs1 ∪ rs2) -> matches_set' s rs1 \/ matches_set' s rs2.
Proof.
  intros. induction H. destruct H as [H1 H2].
  set_unfold. set_solver.
Qed.  

(* Lemma matches_set_cons : forall (r : re) (rs : gset re) (s s' : string),
  matches_set s rs -> 
  matches_set s' {[ r ]} ->
  matches_set (s ++ s') (rs ∪ {[ r ]}). *)


(******************************************************************************)

(* No string matches the empty regex set *)
Lemma not_matches_empty (s : string) : ~(matches_set s ∅).
Proof.
  unfold not. intros.
  inversion H; subst; set_solver.
Qed.  
Hint Resolve not_matches_empty : core.

(* If [s] matches [r], then [s] matches the singleton set containing [r] *)
Lemma matches_singleton' (s : string) (r : re) : 
  matches r s -> matches_set s {[ r ]}.
Proof.
  intros; eapply matches_set_here; eauto; set_solver.
Qed.  

Lemma singleton_union : forall (r1 r3 : re) (rs : gset re),
  {[ r1 ]} ∪ rs = {[ r3 ]} -> r1 = r3.
Proof. 
  intros. set_solver.
Qed.  

(* If a string [s] matches a singleton set containing [r], then it's the same
   as just saying [matches r s] *)
(* Lemma matches_singleton (s : string) (r : re) : 
  matches_set s {[ r ]} -> matches r s.
Proof. 
  intros; inversion H; subst. 
  - (* matches_set_here *)
    cut (r0 = r). intros. subst. assumption. set_solver.
Admitted. *)

(* The empty string matches the singleton set containing [Epsilon] *)
Lemma matches_set_epsilon : matches_set [] {[Epsilon]}.
Proof.
  eapply matches_set_here.
  - apply matches_epsilon.
  - set_solver.
Qed.


Lemma a_der_matches_1 a r s : matches_set' s (a_der r a) -> matches r (a :: s).
Proof. 
  revert s.
  induction r; X; try (apply not_matches_empty in H; destruct H).
  - (* Concat *)
    eapply matches_concat.
    apply isEmpty_matches_1 in Heqb.
    apply Heqb.
    apply IHr2.
    eexists. split.
    + apply H.
    + apply H0.
    + simpl. reflexivity.
Qed.

(* Lemma a_der_matches_2 a r s : matches r (a :: s) -> matches_set' s (a_der r a).
Proof.
  revert s. intros.
  induction r; X; eexists.
Admitted.  *)