open Lib
open Antimirov
open Sexplib.Conv

(** Deprecated example: Runs the staged regex matcher (from Filinski section 3) 
on the empty string for matching `ε*`. The compiled program is:
  {[ 
    (((true AtEnd) (false (Or (Cont true (CN 0)) (Cont false (CN 2))))
      (true (Cont true (CN 1)))
      (true (Or (Cont true (CN 0)) (Cont false (CN 2)))))
    (CN 3))
    result = true
  ]} *)
let filinski_test () =
  let open Filinski in 
  let b = imatchtop (Star Eps) "" in
  Stdio.printf "result = %b\n" b


(** Runs a QuickCheck test which {i falsifies} the property that Brzozowski 
    derivatives are always contained in non-empty sets of Antimirov derivatives *)
let () = 
  Core.Quickcheck.test ~seed:`Nondeterministic gen_re_char_nonempty_antimirov 
  ~shrinker:shrink_re_char
  ~sexp_of:(fun (r, c) -> List [sexp_of_re r; sexp_of_char c])
  ~f:(fun ((r, c) : re * char) -> 
    let antimirov_set = aderiv_opt c r in 
    assert (R.mem (bderiv_opt r c) antimirov_set))

