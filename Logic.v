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

(* Sequent calculus version:

Split judgment (A is true) into two judgments: A is a resource; A is a goal
Resources: factories (unrestricted); normal (linear)

Rules: right rule (goal) = intro rule; (??) -- this corresponds directly!
       left rule (resource) = elim rule (oh... stuff you have in context)
         -- 
       so like inversion? does that need to be explicitly encoded?


In the rules, why doesn't Pfenning label with whether they are factories or normal (restricted)???

Two cut rules?? Some stuff about coercion?? *)

(* 
- ILL props
- ILL connectives
- Notations for them
- ILL rules (sequents)
- Notations for them
*)

(*
ILL connectives: note, some are binary, some are unary, some are nullary

(- Atomic proposition -- only in ILL paper -- with type Vars.t = N)

* Multiplicative
- Linear implication -o
- Simultaneous conjunction ((X)) or ** (times)
- Multiplicative truth: 1

* Additive
- Alternative conjunction (&) (with)
- Plus (+)
- True
- 0

* Quantifiers?
- forall
- exists

* Exponentials?
- subset
- bang

so we don't need to model classical props? what about factories? shouldn't we distinguish between linear and classical/unlimited props? ILinProp = Resource... could encode using bang?

(ILL props just have type ILinProp
- Name? How to represent the prop A?
- it DOESN'T MATTER what value inhabits type ILinProp! for example, we have "empty : ILinProp"
)
 *)

(* ILL rules:

Gamma |- A, B...N not possible -- only
Gamma |- A? (where A = A (+) B... if necessary)

so Gamma |- A = LinCons (or Turnstile) (Gamma/Resources : list ILinProp) (A : ILinProp) : Prop

so, how can you construct/prove? a (single-consequent) sequent in ILL?
well, if you want to construct/prove something of form (d1, d2, A -o B) |- C,
  you can do it by constructing/proving two things
  one of form (D1 |- A), another of form (d2 ^ B |- C)...

and so on for each rule!

*)

