open! Base

(* --------------------- Section 3: A Matching Algorithm -------------------- *)

(** A datatype for regular expressions *)
type regexp = 
  | Zero 
  | One 
  | Char of char 
  | Times of regexp * regexp
  | Plus of regexp * regexp 
  | Star of regexp 

(** [acc] matches some initial segment of [cs] against the regex [r],
    and pases the corresponding final segment to the continuation [k] *)
let rec acc (r : regexp) (cs : char list) (k : char list -> bool) : bool = 
  match r, cs with 
  | Zero, _ -> false 
  | One, _ -> k cs 
  | Char _, [] -> false 
  | Char d, c :: cs -> if Char.equal c d then k cs else false 
  | Plus (r1, r2), _ -> 
    acc r1 cs k || acc r2 cs k 
  | Times (r1, r2), _ -> 
    acc r1 cs (fun cs' -> acc r2 cs' k)
  | Star r1, _ -> 
    k cs || acc r1 cs (fun cs' -> acc r cs' k)

(** Determines whether a string matches a regex *)    
let accept (r : regexp) (s : string) : bool = 
  acc r (String.to_list s) List.is_empty


