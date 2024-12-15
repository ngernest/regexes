# Verifying Brzozowski & Antimirov Derivatives

*Derivatives* of regular expressions are an elegant and algebraic technique, beloved by functional programmers, for implementing regex matching. 

This technique originated from Janusz Brzozowski (1962). Brzozowski's insight was that  given a regex $r$ and the first character $c$ in the input string, the *derivative* of $r$ with respect to $c$, denoted $\delta_c(r)$, is another regex which matches the remainder of the string. Now, suppose we iteratively compute derivatives for each character in the string $s$. If the final regex accepts the empty string $\epsilon$, then $s$ must have matched the original regex $r$! Brzozowski derivatives can be implemented pretty easily in functional languages, as shown in [this blogpost](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) by Harry Goldstein. 

In 1995, Valentin Antimirov introduced an alternative to Brzozowski's method using *partial derivatives*. A partial derivative of $r$ with respect to $c$ is a regex $r'$ such that if $r'$ accepts a string $s$, then $r$ accepts $c\cdot s$. The Antimirov derivative of $r$ with respect to $c$, denoted $\alpha_c(r)$, is a *set* of partial derivatives.

The idea is that the Antimirov derivative should collectively accept the same strings as the Brzozowski derivative. Antimirov derivatives also lend themselves to a concise implementation, as Neel Krishnaswami shows in [this blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html).  

In this project, our broad aim is to mechanize proofs that relate the two notions of derivatives.

One avenue we're exploring is to prove that two implementations of regex matchers, based on Brzozowski and Antimirov derivatives respectively, accept the same set of strings (and are equivalent with respect to an inductive relation that specifies what it means for a string to match a regex). 

Furthermore, Michael Greenberg has a [blogpost](https://www.weaselhat.com/post-819.html) in which he investigates how the *size* of a regex grows as we take successive Brzozowski derivatives. He obtained the following two results empirically (and later [proved them in Coq](https://github.com/Pomona-College-CS181-SP2020/regularity/blob/master/analysis/analysis.v)):
1. There does not exist any constant that bounds the size increase of Brzozowski derivatives (i.e. the size of Brzozowski derivatives grows exponentially).
2. The *height* (of the binary tree representation) of a Brzozowski derivative is at most twice the height of the original regex.
   
We aim to prove similar results for Antimirov derivatives. Thus far, we've proved that (2) also holds for Antimirov derivatives if we consider the *max* height of all terms contained within the set of derivatives. 

Moreover, we aim to explore some recent results published in Romain Edelmann's [PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content) from EPFL. In his thesis, Edelmann shows how Brzozowski derivatives can be implemented using a purely functional data structure called a [zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)). We'd like to prove that the zipper representation of Brzozowski derivatives is equivalent to the typical syntactic presentation of derivatives. Additionally, Edelmann mentions in passing that his zipper representation is "reminiscent of Antimirov derivatives." We'd like to examine whether we can formally prove Edelmann's observation, i.e. that the set of terms contained within a Brzozowski zipper is the same as the set of terms contained in the set of Antimirov derivatives (modulo some rewrite rules). 

In addition, it is known that Brzozowski and Antimirov derivatives are both finite. We would like to prove this result in Coq. Edelmann proves in his thesis that Brzozowski derivatives are finite using some results regarding the finiteness of zippers. It would be interesting to see if we could build on this result when proving finiteness. 
