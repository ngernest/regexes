open Lib.Filinski

let () =
  let b = imatchtop (Star Eps) "" in
  Stdio.printf "result = %b\n" b
