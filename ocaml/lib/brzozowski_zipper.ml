
(* Translated from the Scala code in Romain Edelmann's PhD thesis:
   https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content *)

(** A datatype for regexes *)   
type regex = 
  | Failure 
  | Epsilon 
  | Char of char
  | Sequence of regex * regex 
  | Disjunction of regex * regex 
  | Star of regex
  
(** Checks if a regex accepts the empty string *)  
let rec is_nullable (r : regex) : bool = 
  match r with 
  | Failure | Char _ -> false 
  | Epsilon | Star _ -> true 
  | Disjunction (r1, r2) -> is_nullable r1 || is_nullable r2 
  | Sequence (r1, r2) -> is_nullable r1 && is_nullable r2 

(** A [context] is a list of [regex]es. 
    Semantically, these represent {i sequences} of regexes, specifically 
    all regexes that follow after the focal point. *)
type context = regex list 

(** A [zipper] is a set of [context]s, 
    i.e. [Zipper.t = context Set.t = (regex list) Set.t]. 
    Semantically, zippers represent {i disjunctions} of lists of regexes 
    that arise when deriving. *)
module Zipper = Set.Make(struct
  type t = context 
  let compare = compare
end)

(** Converts a [zipper] to a [regex] *)
let unfocus (zipper : Zipper.t) : regex = 
  (* Converts a singular [context] to a [regex] *)
  let uncontext (ctx : context) : regex = 
    List.fold_left (fun r acc -> Sequence (r, acc)) Epsilon ctx in 
  Zipper.fold 
    (fun ctx acc -> Disjunction (acc, uncontext ctx))
    zipper
    Failure

(** Creates a zipper from a regex *)    
let focus (r : regex) : Zipper.t = Zipper.of_list [[r]]

(* Theorem 2.1
   Round-trip property, where [~=] denotes a regex matching a string
   [{
      forall (r : regex) (cs : list char), 
      unfocus (focus r) ~= cs <--> r ~= cs
   }] *)

(** Variant of Brzozowski derivatives for zipeprs *)
let derive (zipper : Zipper.t) (c : char) : Zipper.t = 
  (** Move the focus up the regex to all subterms that can be reached without 
     consuming any input:
     - [up] stops processing when it reaches a non-nullable regex *)
  let rec up (ctx : context) : Zipper.t = 
    begin match ctx with 
    | [] -> 
        Zipper.empty 
    | right :: parent when is_nullable right -> 
        Zipper.union (down right parent) (up parent)
    | right :: parent -> 
        down right parent 
    end
  (** Moves the focus down the regex *)
  and down (r : regex) (ctx : context) : Zipper.t = 
    begin match r with 
    | Char d when d = c ->
        (* When a context matches a [Char], we collect them in a set
           and form the resulting [zipper] using this set *) 
        Zipper.singleton ctx
    | Disjunction (left, right) -> 
        Zipper.union (down left ctx) (down right ctx)
    | Sequence (left, right) when is_nullable left -> 
        Zipper.union (down left (right :: ctx)) (down right ctx)
    | Sequence (left, right) -> 
        down left (right :: ctx)
    | Star r' -> 
        down r' (r :: ctx)
    | _ -> Zipper.empty
    end in 
  (* if OCaml had [concatMap] for sets, 
    this would just be [Zipper.concatMap up zipper] *)
  Zipper.map (fun ctx -> List.concat @@ Zipper.to_list (up ctx)) zipper
  
(* Theorem 2.2:
  [{ forall (z : zipper) (c : char) (cs : char list), 
    unfocus (derive z c) ~= cs <--> unfocus z ~= c :: cs
  }]   *)

(** Derives by all characters in the argument [char list] *)
let derive_word (zipper : Zipper.t) (cs : char list) : Zipper.t = 
  List.fold_left derive zipper cs

(* Theorem 2.3 
  {[ forall (z : zipper) (cs1 cs2 : char list),
     unfocus (derive_word (z, cs1)) ~= cs2 <--> unfoucs z ~= cs1 ++ cs2 ]}
*)  

(** To check if a [zipper] accepts the empty string,
    check if it contains a context that only consists of nullable regexes *)
let zipper_is_nullable (zipper : Zipper.t) : bool = 
  Zipper.exists (fun ctx -> List.for_all is_nullable ctx) zipper

(* Theorem 2.4
   {[ forall (z : zipper),
      zipper_is_nullable z = true <-> unfocus z ~= ""
   ]}
*)  

(** Checks whether a string matches a regex using zippers 
    (converts the regex into a zipper using [focus], computes 
    its derivative over the string, and then checks whether 
    the resultant zipper accepts the empty string) *)
let accepts (r : regex) (cs : char list) : bool = 
  zipper_is_nullable (derive_word (focus r) cs)

(* Theorem 2.5
   {[ forall (r : regex) (cs : char list),
      accepts r cs = true <--> r ~= cs
   ]}
*)  


(** Takes a zipper [z] and constructs a {i maximal zipper} from it *)
let max_zipper (z : Zipper.t) : Zipper.t = 
  let rec up (ctx : context) : Zipper.t = 
    begin match ctx with 
    | [] -> Zipper.empty 
    | right :: parent -> Zipper.union (down right parent) (up parent)
    end 
  and down (r : regex) (ctx : context) : Zipper.t = 
    begin match r with 
    | Char _ -> 
        Zipper.singleton ctx 
    | Disjunction (left, right) -> 
        Zipper.union (down left ctx) (down right ctx)
    | Sequence (left, right) -> 
        Zipper.union (down left (right :: ctx)) (down right ctx)
    | Star r' -> 
        down r' (r :: ctx)
    | _ -> Zipper.empty 
    end in 
    Zipper.map (fun ctx -> List.concat @@ Zipper.to_list (up ctx)) z

(* 
  Lemma 2.1: 
  {[ forall (z : zipper) (c : char), derive z c ⊆ maxZipper z ]}
  
  Lemma 2.2 (derivation is monotonic wrt maxZipper inclusion):
  {[ forall (z : zipper) (c : char), maxZipper (derive z c) ⊆ maxZipper z }]
  
  Lemma 2.3 
  {[ forall (z : zipper) (cs : char list), cs <> [] -> 
       deriveWord z cs ⊆ maxZipper z ]}

  Theorem 2.6: (finiteness)
  {[ forall (z : zipper), 
       exists (Z : context set), 
         forall (cs : char list),
           deriveWord z cs ⊆ Z 
  ]}
*)

(* Counting contexts (from section 2.6): 
- The set [Z] in Theorem 2.6 can be constructed as [z] union with [maxZipper z].
- The no. of zippers that can e encountered starting from any regex [r] is at most 
  $$ 1 + 2 ^ |maxZipper (focus r)| $$
- The constant $1$ represents the unique context in [focus r],
  while the term $2 ^ |maxZipper (focus r)|$ represents the no. of subsets 
  in [maxZipper (focus r)]. 

- The size of [maxZipper (focus r)] is also bounded by the no. of [Character]
  AST nodes in the original regex [r]
*)