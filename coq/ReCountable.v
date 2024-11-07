Require Import Regex.

(* In order to use sets, we need to prove that regexes have 
   decidable equality and are countable *)

(* Injection from re to nat *)
Definition encode_pair_pos (p : positive * positive) : positive := encode p.
Definition encode_ascii (p : ascii) : positive := encode p.
Definition decode_pair_pos (p : positive) : option (positive * positive) := decode p.
Definition decode_ascii (p : positive) : option ascii := decode p.

Fixpoint encode_regex (r : re) : gen_tree nat :=
  match r with
  | Void => GenLeaf 1
  | Epsilon => GenLeaf 2
  | Atom a => GenNode 3 [GenLeaf (nat_of_ascii a)]
  | Union r1 r2 => GenNode 4 [encode_regex r1; encode_regex r2]
  | Concat r1 r2 => GenNode 5 [encode_regex r1; encode_regex r2]
  | Star r' => GenNode 6 [encode_regex r']
  end.

Search "gen_tree".
Check (gen_tree_countable).
Search "ascii".

Fixpoint decode_regex (t : gen_tree nat) : option re := 
  match t with
  | GenLeaf 1 => Some Void
  | GenLeaf 2 => Some Epsilon
  | GenNode 3 [GenLeaf n] => Some (Atom (ascii_of_nat n))
  | GenNode 4 [r1; r2] =>
    match decode_regex r1, decode_regex r2 with
    | Some r1', Some r2' => Some (Union r1' r2')
    | _, _ => None
    end
  | GenNode 5 [r1; r2] => 
    match decode_regex r1, decode_regex r2 with
    | Some r1', Some r2' => Some (Concat r1' r2')
    | _, _ => None
    end
  | GenNode 6 [r] => 
    match decode_regex r with
    | Some r' => Some (Star r')
    | _ => None
    end
  | _ => None
  end.

Theorem decode_encode_regex (r : re) : decode_regex (encode_regex r) = Some r.
Proof. 
  induction r; unfold decode_regex; unfold encode_regex; 
  eauto; fold decode_regex; fold encode_regex.
  - rewrite ascii_nat_embedding. reflexivity.
  - rewrite IHr1, IHr2. reflexivity.
  - rewrite IHr1, IHr2. reflexivity.
  - rewrite IHr. reflexivity.
Qed.

Instance ReCountable : Countable re.
Proof. 
  apply inj_countable with (f := encode_regex) (g := decode_regex). 
  intros. apply decode_encode_regex.
Qed.
