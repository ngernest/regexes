(* Translated from the Scala code in Romain Edelmann's PhD thesis:
   https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content 
   (section 2.5) *)

(** Datatype for binary trees *)
type 'a tree = 
  | Leaf of 'a
  | Branch of 'a tree * 'a tree

(** The context represents the path taken to reach current subtree in focus *)
type 'a context =
  | Empty
  | InLeft of 'a tree * 'a context  (* right tree and parent context *)
  | InRight of 'a tree * 'a context (* left tree and parent context *)

(** A Zipper consists of a focused tree and a context *)
type 'a zipper = {
  focus: 'a tree;
  context: 'a context;
}

(** Helper to create a zipper *)
let focus (tree : 'a tree) : 'a zipper = {
  focus = tree;
  context = Empty;
}

(** Moves the focus to the parent node (constant-time) *)
let move_up (zipper : 'a zipper) : 'a zipper = 
  match zipper.context with
  | Empty -> zipper
  | InLeft (right, parent) -> 
    { focus = Branch (zipper.focus, right);
      context = parent }
  | InRight (left, parent) -> 
    { focus = Branch (left, zipper.focus);
      context = parent }

(** Reconstruct the full tree from a zipper *)
let rec unfocus (zipper : 'a zipper) : 'a tree = 
  match zipper.context with
  | Empty -> zipper.focus
  | InLeft (right, parent) -> 
      unfocus { 
        focus = Branch (zipper.focus, right);
        context = parent 
      }
  | InRight (left, parent) -> 
      unfocus {
        focus = Branch (left, zipper.focus);
        context = parent 
      }

(** Moves the focus to the left child if possible (constant-time) *)
let move_left (zipper : 'a zipper) : 'a zipper = 
  match zipper.focus with
  | Leaf _ -> zipper
  | Branch (left, right) -> 
      { focus = left;
        context = InLeft (right, zipper.context) }

(** Moves the focus to the right child if possible (constant-time) *)
let move_right (zipper : 'a zipper) : 'a zipper  = 
  match zipper.focus with
  | Leaf _ -> zipper
  | Branch (left, right) -> 
      { focus = right;
        context = InRight (left, zipper.context) }

(** Replaces the focus with a new tree *)
let replace_focus (zipper : 'a zipper) (new_focus : 'a tree) : 'a zipper = 
  { zipper with focus = new_focus }