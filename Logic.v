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
- with manual proof *)

(* Sequent calculus version:

Split judgment (A is true) into two judgments: A is a resource; A is a goal
Resources: factories (unrestricted); normal (linear)

Rules: right rule (goal) = intro rule; (??) -- this corresponds directly!
       left rule (resource) = elim rule (oh... stuff you have in context)
       so like inversion? does that need to be explicitly encoded?

In the rules, why doesn't Pfenning label with whether they are factories or normal (restr.)???

Two cut rules?? Some stuff about coercion?? *)

(* - ILL props
- ILL connectives
- Notations for them
- ILL rules (sequents)
- Notations for them *)

(* so we don't need to model classical props? what about factories? shouldn't we distinguish between linear and classical/unlimited props? ILinProp = Resource... could encode using bang?

(ILL props just have type ILinProp
- Name? How to represent the prop A?
- it DOESN'T MATTER what value inhabits type ILinProp! e.g. we have "empty : ILinProp") *)

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


Module LinearLogic.

Require Import Coq.Sets.Multiset.
Set Implicit Arguments.

Definition Var : Type := nat.

(* ILL connectives -- combination of those given by Pfenning + AGB's encoding *)
Inductive formula : Type :=
  (* Atomic *)
  | LProp : Var -> formula
  (* Multiplicative *)
  | Implies : formula -> formula -> formula (* -o *)
  | Times : formula -> formula -> formula (* (X) *)
  | One : formula                         (* Multiplicative identity TODO *)
  (* Additive *)
  | With : formula -> formula -> formula (* & *)
  | Plus : formula -> formula -> formula (* (+) *)
  | Top : formula                        (* aka True? *)
  | Zero : formula                       (* Additive identity TODO *)
  (* Exponentials *)
  | Bang : formula -> formula   (* TODO *)
  (* implication/arrow TODO *)
.

Check (LProp 5).
Definition A := LProp 0.
Definition B := LProp 1.
Definition C := LProp 2.

(* TODO change levels and associativity *)
Notation "A -o B" := (Implies A B) (at level 100, right associativity).
Notation "A ** B" := (Times A B) (at level 100, right associativity).
(* TODO figure out how to override && and ++ *)
Notation "A && B" := (With A B) (at level 40, left associativity).
Notation "A ++ B" := (Plus A B) (at level 60, right associativity).
Notation "!A" := (Bang A) (at level 200, right associativity).

(* TODO environment type: multiset? list? + environment notations *)

Definition env : Type := multiset formula.

Definition env1 : env := EmptyBag formula.

Definition eqFormula (f1 : formula) (f2 : formula) :=
  match f1, f2 with
    | LProp v1, LProp v2 => v1 = v2
    | _, _ => False
  end. (* TODO *)
Lemma eq_neq_formula : forall (f1 f2 : formula),
                         {eqFormula f1 f2} + {~ eqFormula f1 f2}.
Proof.
Admitted.

Definition singleton := SingletonBag eqFormula eq_neq_formula.
Definition env2 := singleton A.

Notation "{A}" := (singleton A) (at level 200, right associativity).
Notation "S1 == S2" := (meq S1 S2) (at level 100, right associativity).
Notation "g1 'U' g2" := (munion g1 g2) (at level 100, right associativity).
Notation "A :: g" := (munion (singleton A) g) (at level 60, right associativity).

Check (env1 == env2).

(* hopefully don't need to deal with list equality modulo permutation *)

Reserved Notation "A '|-' B" (at level 40).
(* Here, (->) denotes (--------) *)
(* convention: env name lowercase, prop name uppercase *)
Inductive ILL_proof : env -> formula -> Prop :=
  | Id : forall (g : env) (A : formula),
           (g == {A}) ->
           g |- A

  (* Multiplicative connectives *)
  | Impl_R : forall (g : env) (A B : formula),
              (A :: g) |- B ->
              g |- (A -o B)

  (* | Impl_L : forall (g d1 d2 : env) (A B C : formula), *)
  (*             (g ++ d1) |- A -> *)
  (*             (g ++ d2 *)

  where "x |- y" := (ILL_proof x y).



End LinearLogic.
