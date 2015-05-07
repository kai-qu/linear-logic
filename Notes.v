(* so we don't need to model classical props? what about factories? shouldn't we distinguish between linear and classical/unlimited props? ILinProp = Resource... could encode using bang?

(ILL props just have type ILinProp
- Name? How to represent the prop A?
- it doesn't matter what value inhabits type ILinProp! e.g. we have "empty : ILinProp") *)

(* ILL rules:

Gamma |- A, B...N not possible -- only
Gamma |- A? (where A = A (+) B... if necessary)

so Gamma |- A = LinCons (or Turnstile) (Gamma/Resources : list ILinProp) (A : ILinProp) : Prop

so, how can you construct/prove? a (single-consequent) sequent in ILL?
well, if you want to construct/prove something of form (d1, d2, A -o B) |- C,
  you can do it by constructing/proving two things
  one of form (D1 |- A), another of form (d2 ^ B |- C)...

and so on for each rule! *)

(* ILL connectives: note, some are binary, some are unary, some are nullary
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
- exists -- TODO: actually, these are rules. also, I think they're built into Coq...
  unless the linear quantifier rules are different?

* Exponentials?
- subset
- bang *)
