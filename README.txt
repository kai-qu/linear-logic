kye
5/6/15
Project README

Progress:

- Read "Working with Linear Logic in Coq" (WLLC)
- Read chapters 1 and 3 of Pfenning's linear logic notes (PLL)
- Read "Toward Language-Based Verification of Robot Behaviors" (LBV)
- Skimmed "Structural Analysis of Narratives with the Coq Proof Assistant" (SAN)
- Skimmed Wadler's linear logic notes

- Picked a version of linear logic to use (sequent calculus with bangs and the cut rule)
- Encoded that version, combining environment techniques from SAN with the rules from PLL and the scenario from WLLC
- Finished intuitionistic linear logic connectives, rules, notations
- Started working on the blocks world: encoded states, axioms, beginning lemmas to prove, and final theorem to prove.
  In process of proving the first lemma.
- Some problems with the environment definition. Need a multiset with setoid rewrite and element removal. 
  Looked into multisets vs. ensembles vs. listsets vs. plain lists. Picked multisets.

TODO: 

- Figure out how to do setoid rewrites with multisets
- Possibly adjust ILL rules to make working with environments easier
- Prove environment lemmas
- Prove the 3 blocks world lemmas
- Prove the final blocks world lemma
- Add automation to this scenario 
(by Saturday?)

- Pick a new scenario related to games or narratives
- Encode it 
- Add automation
(by Wednesday?)

Difficulties:

- setoid rewrite, environment manipulation
- inversion on ILL rules doesn't give the intended results
- still thinking about new scenarios (narratives/games) to encode. Any suggestions? 
  One direction is something Tetris-like; another direction is something "Madame Bovary"-like