open Lib
open Regex
open Antimirov
open Sexplib.Conv

(** Runs a QuickCheck test which {i falsifies} the property that Brzozowski 
    derivatives are always contained in non-empty sets of Antimirov derivatives. 
    - We generate pairs [(r, c)] of regexes and chars for which the set 
    of Antimirov derivatives is non-empty, and then we check whether 
    the Brzozowski derivative of [r] w.r.t [c] is contained in the Antimirov set *)
let () = 
  Core.Quickcheck.test ~seed:`Nondeterministic gen_re_char_nonempty_antimirov 
  ~shrinker:shrink_re_char
  ~sexp_of:(fun (r, c) -> List [sexp_of_re r; sexp_of_char c])
  ~f:(fun ((r, c) : re * char) -> 
    let antimirov_set = aderiv_opt c r in 
    assert (RegexSet.mem (Brzozowski.bderiv_opt r c) antimirov_set))

