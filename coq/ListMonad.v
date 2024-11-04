(* Taken from Lecture 10 code *)
Require Import String.
Open Scope string_scope.
Require Import List.
Export ListNotations.
Open Scope list_scope.

(******************************************************************************)
(** Monad notation *)

(* The [Monad] typeclass *)
Class Monad (M : Type -> Type) := {
  ret : forall {A : Type}, A -> M A ; 
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B
}.

(* Notation for monadic bind *)
Notation "x <- c1 ;; c2" :=
  (bind c1 (fun x => c2)) 
    (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" :=
  (bind c1 (fun _ => c2)) (at level 100, right associativity).

(******************************************************************************)
(** Defining the list monad *)

(* Flattens a list of lists into a single list *)
Definition concat {A:Type} (xs:list (list A)) : list A := 
  fold_right (fun x a => x ++ a) [] xs.

(* The List monad: note that [bind] is just [concatMap] *)
Instance listMonad : Monad list := {
  ret := fun {A:Type} (x : A) => [x];
  bind := fun {A B:Type} (xs : list A) (f: A -> list B) => 
            concat (map f xs)
}.

(* [concat] distributes over [++] *)
Lemma concat_app : forall {A : Type} (l l' : list (list A)),
  concat (l ++ l') = (concat l) ++ (concat l').
Proof.
  induction l as [| x xs IHxs]; intros.
  - (* l = [] *)
    reflexivity.
  - (* l = x :: xs *)
    simpl. rewrite IHxs. 
    rewrite List.app_assoc. reflexivity.
Qed.    

(******************************************************************************)
(** Monad laws *)

(* Typeclass specifying the Monad laws *)
Class Monad_with_Laws (M : Type -> Type) {MonadM : Monad M} := {
  m_left_id : forall {A B : Type} (x : A) (f: A -> M B),
    bind (ret x) f = f x ;
  m_right_id : forall {A B : Type} (c : M A),
    bind c ret = c ;
  m_assoc : forall {A B C} (c : M A) (f : A -> M B) (g : B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)
}.  

(* Proving that [return x >>= f === f x] for the list monad *)
Lemma list_left_id : forall {A B : Type} (x : A) (f : A -> list B),
  bind (ret x) f = f x.
Proof.
  intros.  
  simpl. rewrite app_nil_r.
  reflexivity.
Qed.  

(* Proving that [xs >>= return === xs] for the list monad *)
Lemma list_right_id : forall {A B : Type} (xs : list A),
  bind xs ret = xs.
Proof.
  intros.
  induction xs as [| x xs' IHxs']; simpl in *.
  - (* xs = [] *)
    reflexivity.
  - (* xs = x :: xs' *)
    f_equal. apply IHxs'.
Qed.    

(* Proving that [(xs >>= f) >>= g === xs >>= (\x -> f x >>= g)] *)
Lemma list_assoc : forall {A B C} 
  (xs : list A) (f : A -> list B) (g : B -> list C),
  bind (bind xs f) g = bind xs (fun x => bind (f x) g).
Proof.
  intros.
  induction xs as [| x xs' IHxs']; simpl in *.
  - (* xs = [] *)
    reflexivity.
  - (* xs = x :: xs' *)
    rewrite <- IHxs'.
    (* [map] distributes over [++] *)
    rewrite List.map_app.
    (* [concat] distributes over [++] *)
    rewrite concat_app.
    reflexivity.
Qed.    

(* The list monad satisfies the monad laws! *)
Instance ListMonadLaws : @Monad_with_Laws list _ := {
    m_left_id := @list_left_id;
    m_right_id := @list_right_id;
    m_assoc := @list_assoc
  }.


    
  
