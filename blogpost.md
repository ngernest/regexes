# Verifying Brzozowski & Antimirov Derivatives

*Derivatives* of regular expressions are an elegant and algebraic technique 
for implementing regex matching, beloved by functional programmers. 

This technique originated from Janusz Brzozowski (1962). Brzozowski's insight was that 
given a regex $r$ and the first character $c$ in the input string, the *derivative* of $r$ with respect to $c$, denoted $\delta_c(r)$, is another regex which matches the remainder of the string. Then, suppose we repeatedly compute derivatives for each character in the string $s$. If the final regex accepts the empty string $\epsilon$, then $s$ must have matched the original regex $r$! Brzozowski derivatives can be implemented pretty easily in functional languages, as shown in [this blogpost](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) by Harry Goldstein. 

In 1995, Valentin Antimirov introduced an alternative to Brzozowski's method, which consists of *partial derviatives*. Antimirov's idea was that sets of partial derivatives should collectively accept the same strings as the Brzozowski derivative. Antimirov derivatives also lend themselves to a concise implementation, as Neel Krishnaswami shows in [this blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html).  

In this project, our aim is to mechanize proofs that relate the two notions of derivatives.
- Can we prove that Brzozowski and Antimirov-based regex matchers accept the same strings? 
- Are both Brzozowski and Antimirov derivatives finite? 
- Can we achieve similar bounds regarding the size of both types of derivatives? 






