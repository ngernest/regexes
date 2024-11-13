# Verifying Brzozowski & Antimirov DerivativeS

*Derivatives* of regular expressions are an elegant and algebraic technique 
for implementing regex matching, beloved by functional programmers. 

This technique originated from Janusz Brzozowski (1962). Brzozowski's insight was that 
given a regex $r$ and the first character $c$ in the input string, the *derivative* of $r$ with respect to $c$, denoted $\delta_c(r)$, is another regex which matches the remainder of the string. Then, suppose we repeatedly compute derivatives for each character in the string $s$. If the final regex accepts the empty string $\epsilon$, then $s$ must have matched the original regex $r$! 


However, in 1995, Valentin Antimirov introduced an alternative method consisting of *partial derviatives*. Antimirov's idea was that sets of partial derivatives should collectively accept the same strings as the Brzozowski derivative.


Accessible introductions to the Brzozowski and Antimirov derivatives can be found in [these](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) [two](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html) blogposts by [Harry Goldstein](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) and [Neel Krishnaswami](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html) respectively. 






