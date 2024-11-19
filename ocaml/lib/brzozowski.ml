open Regex 

(** [bderiv re c] takes the Brozozowski derivative of the regex [re] 
      with respect to the char [c] *)
let rec bderiv (re : re) (c : char) : re =
  match re with
  | Void | Epsilon -> Void
  | Char c' when c = c' -> Epsilon
  | Char _ -> Void
  | Alt (r1, r2) -> Alt (bderiv r1 c, bderiv r2 c)
  | Seq (r1, r2) ->
    if accepts_empty r1 
      then Alt (Seq (bderiv r1 c, r2), bderiv r2 c)
    else 
      Seq (bderiv r1 c, r2)
  | Star r -> Seq (bderiv r c, Star r)
    
(** Optimized version of [bderiv] that uses smart constructors *)
let rec bderiv_opt (re : re) (c : char) : re =
  match re with
  | Void | Epsilon -> Void
  | Char c' when c = c' -> Epsilon
  | Char _ -> Void
  | Alt (r1, r2) -> alt (bderiv_opt r1 c) (bderiv_opt r2 c)
  | Seq (r1, r2) ->
    if accepts_empty r1 
      then alt (seq (bderiv_opt r1 c) r2) (bderiv_opt r2 c)
    else 
      seq (bderiv_opt r1 c) r2
  | Star r -> seq (bderiv_opt r c) (star r)

(** Uses Brzozowski derivatives to determine whether the string [s] 
  matches the regex [r] *)  
let brzozowski_match (r : re) (s : string) : bool =
  accepts_empty (String.fold_left (fun r c -> bderiv r c) r s)
