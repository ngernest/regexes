# Verifying Brzozowski & Antimirov Derivatives

*Derivatives* of regular expressions are an elegant and algebraic technique, beloved by functional programmers, for implementing regex matching. 

The technique originated from Janusz Brzozowski (1962). Brzozowski's insight was that  given a regex $r$ and the first character $c$ in the input string, the *derivative* of $r$ with respect to $c$, denoted $\delta_c(r)$, is another regex which matches the remainder of the string. Now, suppose we iteratively compute derivatives for each character in the string $s$. If the final regex accepts the empty string $\epsilon$, then $s$ must have matched the original regex $r$! Brzozowski derivatives can be implemented pretty easily in functional languages, as shown in [this blogpost](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) by Harry Goldstein. 

In 1995, Valentin Antimirov introduced an alternative to Brzozowski's method using *partial derivatives*. A partial derivative of $r$ with respect to $c$ is a regex $r'$ such that if $r'$ accepts a string $s$, then $r$ accepts $c\cdot s$. The Antimirov derivative of $r$ with respect to $c$, denoted $\alpha_c(r)$, is a *set* of partial derivatives.
The idea is that the Antimirov derivative should collectively accept the same strings as the Brzozowski derivative. Antimirov derivatives also lend themselves to a concise implementation, as Neel Krishnaswami shows in [this blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html).  

Moreover, we explored some recent results published in Romain Edelmann's [PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content) from EPFL. In his thesis, Edelmann shows how Brzozowski derivatives can be implemented using a purely functional data structure called a [zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)). Edelmann mentions in passing that his zipper representation is "reminiscent of Antimirov derivatives." We formally proved Edelmann's observation, i.e. that the set of terms contained within a Brzozowski zipper is the same as the set of terms contained in the set of Antimirov derivatives (modulo some rewrite rules). 

In this project, we mechanize proofs that relate the two notions of derivatives and the zipper representation of Brzozowski derivatives.
1. Regex matchers based on Brzozowski and Antimirov derivatives are equivalent, in that they accept exactly the same set of strings. They are also equivalent to an inductively-defined matcher.
2. There are finitely many Antimirov partial derivatives for a given regex. (This means that we can write an algorithm to build a DFA using these derivatives.)
3. Michael Greenberg has a [blogpost](https://www.weaselhat.com/post-819.html) in which he investigates how the *size* of a regex grows as we take successive Brzozowski derivatives. In particular, the size (number of AST nodes) of Brzozowski derivatives grows exponentially, and the *height* (of the AST representation) of a Brzozowski derivative is at most twice the height of the original regex. We proved similar results for the Antimirov derivative:
   
   a. The height of an Antimirov partial derivative is at most twice the height of the original regex.

   b. The number of Antimirov partial deriatives of a regex is linear in the AST size of the original regex. 
4. If we concatenate the elements within each context (list of regexes) contained in Edelmann’s zipper, we get the same set of regexes as the Antimirov derivative.

Thus, we have proved notions of equivalence for Brzozowski-based matchers, Antimirov-based matchers, and the zipper representation of the Brzozowski derivative. 
We also proved bounds on size, height, and finitude for these derivatives. Finally, we also implemented much of our work in OCaml to allow these derivative-based matchers to be executed.
