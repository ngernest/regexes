Require Import Regex.

(* In order to use sets, we need to prove that regexes have 
   decidable equality and are countable *)

(* Injection from re to nat *)
Definition encode_pair_pos (p : positive * positive) : positive := encode p.
Definition encode_ascii (p : ascii) : positive := encode p.
Definition decode_pair_pos (p : positive) : option (positive * positive) := decode p.
Definition decode_ascii (p : positive) : option ascii := decode p.

Fixpoint encode_regex (r : re) : positive :=
  match r with
  | Void => encode (1, 1, 1)
  | Epsilon => encode (2, 2, 2)
  | Atom a => encode (3, a, 3)
  | Union r1 r2 => encode (4, encode_regex r1, encode_regex r2)
  | Concat r1 r2 => encode (5, encode_regex r1, encode_regex r2)
  | Star r' => encode (6, encode_regex r', 6)
  end.

Lemma encode_regex_injective :
  forall r1 r2 : re, encode_regex r1 = encode_regex r2 -> r1 = r2.
Proof. Admitted.

Search "Countable".


Definition my_decode (n : positive) : option (positive * positive * positive) := decode n.
Definition char_decode (n : positive) : option char := decode n.

Search (ascii).
Fixpoint decode_regex (n : positive) : option re := 
  match (decode n) with
  | Some (1%positive, 1%positive, 1%positive) => Some Void
  | Some (2%positive, 2%positive, 2%positive) => Some Epsilon
  | Some (3%positive, a', 3%positive) => 
    match decode a' with
    | Some a => Some (Atom a)
    | _ => None
    end
  (* | Some (4%positive, n1, n2) => 
    match (decode_regex n1, decode_regex n2) with
    | (Some r1, Some r2) => Some (Union r1 r2)
    | _ => None
    end *)
  | _ => None
  end.

Definition decode_encode_regex (r : re) : 
  decode_regex (encode_regex r) = Some r.
Proof. 
  unfold decode_regex, encode_regex. induction r; 
  unfold encode_pair_pos, decode_pair_pos, 
  encode_ascii, decode_ascii; eauto.
Admitted.

Instance ReCountable : Countable re := {
  encode := encode_regex;
  decode := decode_regex;
  decode_encode := decode_encode_regex
}.
