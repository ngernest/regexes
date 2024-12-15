(** Generates 15 random (regex, string) pairs, and shows that the three regex 
    matchers respectively based on Brzozowski / Antimirov / zippers return the same 
    acceptance result *)  
let () = Lib.Three_matchers.three_matchers_demo ()