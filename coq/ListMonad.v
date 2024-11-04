(* Taken from Lecture 10 code *)
Require Import String.
Open Scope string_scope.
Require Import List.
Export ListNotations.
Open Scope list_scope.

(* The [Monad] typeclass *)
Class Monad (M : Type -> Type) := {
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(* Notation for monadic bind *)
Notation "x <- c1 ;; c2" :=
  (bind c1 (fun x => c2)) 
    (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" :=
  (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* Typeclass specifying the Monad laws *)
Class Monad_with_Laws (M: Type -> Type) {MonadM : Monad M} := {
  m_left_id : forall {A B:Type} (x:A) (f:A -> M B),
    bind (ret x) f = f x ;
  m_right_id : forall {A B:Type} (c:M A),
    bind c ret = c ;
  m_assoc : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)
}.  

(* Flattens a list of lists into a single list *)
Definition concat {A:Type} (xs:list (list A)) : list A := 
  fold_right (fun x a => x ++ a) [] xs.

(* The List monad *)
Instance listMonad : Monad list := {
  ret := fun {A:Type} (x:A) => [x];
  bind := fun {A B:Type} (xs : list A) (f: A -> list B) => 
            concat (map f xs)
}.

