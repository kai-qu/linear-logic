kye
COS 510 final project
Due 5/13/15

I read the following papers for background:

- "Working with Linear Logic in Coq" (WLLC)
- chapters 1 and 3 of Pfenning's linear logic notes (PLL)
- "Toward Language-Based Verification of Robot Behaviors" (LBV)
- "Structural Analysis of Narratives with the Coq Proof Assistant" (SAN)
- Wadler's linear logic notes

Each file contains detailed comments on the contents, as well as TODOs. Here's a high-level summary of what I did.

- Learned linear logic
- Picked a version of linear logic to use (intuitionistic; sequent calculus with the cut rule)
- Encoded its connectives, rules, and notations
- This required combining environment techniques from SAN with the rules from PLL and the scenario from WLLC
- Represented the environment as a multiset of linear logic props; learned how to do setoid rewrites
- Formalized the blocks world example: objects, axioms, and proved* the main lemma, SwapAB
- Formalized a new example, that of the box-pushing game Sokoban, and proved* a small Sokoban game

* There are many admitted lemmas throughout the files. They relate almost entirely to manipulating the environment.
  Dealing with interactions between union, singleton, and the connective (**) required a lot of work, and it got tedious.
  The structure of the proofs should be evident though, since I used the linear logic rules, only admitting the env lemmas.

Difficulties

- The environment, setoid rewrites, and dealing with the (**) connective.
  - I think it would make life a lot easier to use a dedicated linear logic proof assistant instead of my shallow embedding of ILL.
    For example, Coq has the context, which is basically the environment e in a sequent (in "e |- g").
    That takes away all the work of dealing with commutativity, associativity, etc. of things in the environment.
- Inversion on linear logic proofs, or doing induction on them, didn't really work. 
  I found it unusually hard to prove things like the following:
  {{ A ** B }} |- g 
  ->
  A :: B :: emptyBag |- g
- Short proofs were long and tedious; could use a lot more automation (to discharge env subgoals) and proof search (to apply ILL rules).

Future directions

- Dedicated ILL proof assistants (Twelf?).
- Invariants of ILL proofs, corresponding to story or game invariants. Some examples:
  There exists a proof such that block C never moves. Or, for all proofs, resource X is always consumed.
  Or, for all proofs of a well-formed Sokoban level (that is, all traces of playing that level), 
  the player never goes out of bounds of the walls.
