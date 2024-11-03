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
  | Empty => encode_pair_pos (1%positive, 1%positive)
  | Epsilon => encode_pair_pos (2%positive, 2%positive)
  | Atom a => encode_pair_pos (3%positive, encode_ascii a)
  | Union r1 r2 => encode_pair_pos
    (4%positive, (encode_pair_pos (encode_regex r1, encode_regex r2)))
  | Concat r1 r2 => encode_pair_pos 
    (5%positive, (encode_pair_pos (encode_regex r1, encode_regex r2)))
  | Star r' => encode_pair_pos (6%positive, (encode_regex r'))
  end.

Definition decode_regex (n : positive) : option re := 
  match (decode_pair_pos n) with
  | Some (1%positive, 1%positive) => Some Empty
  | Some (2%positive, 2%positive) => Some Epsilon
  | Some (3%positive, rest) =>
    match (decode_ascii rest) with
    | Some a => Some (Atom a)
    | None => None
    end
    (* | Some (4, rest) =>
      let (enc_r1, enc_r2) := decode rest in
      match decode_regex enc_r1, decode_regex enc_r2 with
      | Some r1, Some r2 => Some (Union r1 r2)
      | _, _ => None
      end
    | Some (5, rest) =>
      let (enc_r1, enc_r2) := decode rest in
      match decode_regex enc_r1, decode_regex enc_r2 with
      | Some r1, Some r2 => Some (Concat r1 r2)
      | _, _ => None
      end
    | Some (6, rest) =>
      match decode_regex rest with
      | Some r => Some (Star r)
      | None => None
      end *)
    | _ => None
  end.

Definition decode_encode_regex (r : re) : 
  decode_regex (encode_regex r) = Some r.
Proof. 
  unfold decode_regex, encode_regex. induction r; 
  unfold encode_pair_pos, decode_pair_pos, encode_ascii, decode_ascii;
  rewrite ! decode_encode; eauto.
  - 
Admitted.


Instance re_countable : @Countable re re_dec := {
  encode := encode_regex;
  decode := decode_regex;
  decode_encode := decode_encode_regex
}.
