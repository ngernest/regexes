# Verifying Brzozowski & Antimirov Derivatives

*Derivatives* of regular expressions are an elegant and algebraic technique, beloved by functional programmers, for implementing regex matching. 

The technique originated from Janusz Brzozowski (1962). Brzozowski's insight was that  given a regex $r$ and the first character $c$ in the input string, the *derivative* of $r$ with respect to $c$, denoted $\delta_c(r)$, is another regex which matches the remainder of the string. Now, suppose we iteratively compute derivatives for each character in the string $s$. If the final regex accepts the empty string $\epsilon$, then $s$ must have matched the original regex $r$! Brzozowski derivatives can be implemented pretty easily in functional languages, as shown in [this blogpost](https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html) by Harry Goldstein. 

In 1995, Valentin Antimirov introduced an alternative to Brzozowski's method using *partial derivatives*. A partial derivative of $r$ with respect to $c$ is a regex $r'$ such that if $r'$ accepts a string $s$, then $r$ accepts $c\cdot s$. The Antimirov derivative of $r$ with respect to $c$, denoted $\alpha_c(r)$, is a *set* of partial derivatives.
The idea is that the Antimirov derivative should collectively accept the same strings as the Brzozowski derivative. Antimirov derivatives also lend themselves to a concise implementation, as Neel Krishnaswami shows in [this blogpost](https://semantic-domain.blogspot.com/2013/11/antimirov-derivatives-for-regular.html).  

Moreover, we explored some recent results published in Romain Edelmann's [PhD dissertation](https://infoscience.epfl.ch/server/api/core/bitstreams/4fcb9f0f-7ac1-484f-823c-c19de39dd9ff/content) from EPFL. In his thesis, Edelmann shows how Brzozowski derivatives can be implemented using a purely functional data structure called a [zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)), which is used to navigate tree-shaped datatypes (e.g. our regex AST). A zipper consists of a _focused_ subtree $t$ and a *context*, which contains the path taken to reach $t$ along with $t$'s siblings. Here's an illustration:

<p align="center">
   <img src="https://github.com/user-attachments/assets/ac6bebb9-9bd7-4d44-9601-6b478c86f5a3" width="400"/>
</p>        

(Diagram inspired by [Darragh & Adams's ICFP '20 talk](https://www.youtube.com/watch?v=6Wi-Kc6LDhc))

When navigating through our regex AST, we can shift the zipper's focus to a different subtree, which creates a new zipper with an updated context. Edelmann demonstrates in his dissertation that Brzozowski derivatives can be computed using zippers! His idea was to move the zipper's focus and update the context every time the Brzozowski derivative function $\delta_c$ makes a recursive call, with multiple recursive calls corresponding to multiple focuses. 

Edelmann's insight was that the Brzozowski derivative only introduces 2 new kinds of AST constructors, namely $+$ and $\cdot$. Edelmann demonstrates how we can use sets and lists respectively to represent these two operations:
- When we encounter $+$, e.g. when computing $\delta_c(r_1 + r_2)$, we need to split the focus between two subterms, so we use a *set* to keep track of different choices of focus.
- When we encounter $\cdot$, e.g. when computing $\delta_c(r_1 \cdot r_2$), we have to keep the rest of the expression in the context before recursively calling $\delta_c$ on $r_1$. Since order matters for $\cdot$, we use *lists* to represent a sequence of $\cdot$ operations.
- Edelmann's zipper data structure is thus a *set* of *lists*, where the elements in the set represent different choices of focus, and the elements of each list represent subterms to be concatenated. For example, the regex $(r_1 \cdot r_2) + r_3$ corresponds to the zipper `{ [r1, r2], [r3] }`.  

Now, Edelmann mentions in passing that his zipper representation is "reminiscent of Antimirov derivatives." We formally proved Edelmann's observation, i.e. that the set of terms contained within a Brzozowski zipper is the same as the set of terms contained in the set of Antimirov derivatives (modulo some rewrite rules). 

In this project, we mechanize proofs that relate the two notions of derivatives and the zipper representation of Brzozowski derivatives.
1. Regex matchers based on Brzozowski and Antimirov derivatives are equivalent, in that they accept exactly the same set of strings. They are also equivalent to an inductively-defined matcher.
2. There are finitely many Antimirov partial derivatives for a given regex. (This means that we can write an algorithm to build a DFA using these derivatives.)
3. Michael Greenberg has a [blogpost](https://www.weaselhat.com/post-819.html) in which he investigates how the *size* of a regex grows as we take successive Brzozowski derivatives. In particular, the size (number of AST nodes) of Brzozowski derivatives grows exponentially, and the *height* (of the AST representation) of a Brzozowski derivative is at most twice the height of the original regex. We proved similar results for the Antimirov derivative:
   
   a. The height of an Antimirov partial derivative is at most twice the height of the original regex.

   b. The number of Antimirov partial deriatives of a regex is linear in the AST size of the original regex. 
4. If we concatenate the elements within each context (list of regexes) contained in Edelmann’s zipper, we get the same set of regexes as the Antimirov derivative.

Thus, we have proved notions of equivalence for Brzozowski-based matchers, Antimirov-based matchers, and the zipper representation of the Brzozowski derivative. 
We also proved bounds on size, height, and finitude for these derivatives. Finally, we also implemented much of our work in OCaml to allow these derivative-based matchers to be executed. Our code is available on [GitHub](https://github.com/ngernest/regexes).
