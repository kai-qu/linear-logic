(* TODO: encode linear logic 

Goal for Wednesday night:
-- By Sunday night
- read Power paper X
- read acowley paper https://www.seas.upenn.edu/~acowley/papers/TowardsLinear.pdf X
- skim ILL paper  X
- skim Wadler paper X

-- By Mon night (concurrently?)
- actually pfenning's notes are the best
  - natural deduction vs. sequent (bottom-up)
- which ILL?
- how to encode ILL? (props, formulae, proofs...)
- notations

-- By Tues night
- axioms
- auxiliary lemmas
- encode one example (blocks world, tower of hanoi, ?)
- with manual proof


*)

Inductive ILinProp : Set :=
  | Implies : ILinProp -> ILinProp -> ILinProp
  | One : ILinProp
  | Plus : ILinProp -> ILinProp -> ILinProp
  | Times : ILinProp -> ILinProp -> ILinProp
  | Top : ILinProp
  | With : ILinProp -> ILinProp -> ILinProp
  | Zero : ILinProp.

