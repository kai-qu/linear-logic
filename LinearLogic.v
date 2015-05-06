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
- how to encode ILL? (props, LinPrope, proofs...)
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


(* Module LinearLogic. *)

Require Import Coq.Sets.Multiset.
Require Export Coq.Sets.Multiset.
Set Implicit Arguments.

Definition Var : Type := nat.

(* ILL connectives -- combination of those given by Pfenning + AGB's encoding *)
Inductive LinProp : Type :=
  (* Atomic *)
  | LProp : Var -> LinProp
  (* Multiplicative *)
  | Implies : LinProp -> LinProp -> LinProp (* -o *)
  | Times : LinProp -> LinProp -> LinProp (* (X) *)
  | One : LinProp                         (* Multiplicative identity TODO *)
  (* Additive *)
  | With : LinProp -> LinProp -> LinProp (* & *)
  | Plus : LinProp -> LinProp -> LinProp (* (+) *)
  | Top : LinProp                        (* aka True? *)
  | Zero : LinProp                       (* Additive identity TODO *)
  (* Exponentials *)
  | Bang : LinProp -> LinProp   (* TODO *)
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

Definition env : Type := multiset LinProp.

Definition env1 : env := EmptyBag LinProp.

Definition eqLinProp (f1 : LinProp) (f2 : LinProp) :=
  match f1, f2 with
    | LProp v1, LProp v2 => v1 = v2
    | _, _ => False
  end. (* TODO *)
Lemma eq_neq_LinProp : forall (f1 f2 : LinProp),
                         {eqLinProp f1 f2} + {~ eqLinProp f1 f2}.
Proof.
Admitted.

Definition singleton := SingletonBag eqLinProp eq_neq_LinProp.
Definition env2 := singleton A.

Notation "{{ Z }}" := (singleton Z) (at level 5, Z at level 99, right associativity).
Notation "S == T" := (meq S T) (at level 1, left associativity).
Notation "g1 'U' g2" := (munion g1 g2) (at level 100, right associativity).
Notation "Z :: g" := (munion (singleton Z) g) (at level 60, right associativity).

(* Check ({A} == env1). *)

(* hopefully don't need to deal with list equality modulo permutation *)

Reserved Notation "A '|-' B" (at level 0).
(* Here, (->) denotes (--------) *)
(* convention: env name lowercase, prop name uppercase *)
Inductive LinProof : env -> LinProp -> Prop :=
  | Id : forall (g : env) (A : LinProp),
           (meq g {{A}}) ->
           g |- A

  (* Multiplicative connectives *)
  (* gamma = classical resources; delta = linear resources (after Pfenning)
     can I encode this at the type level? TODO *)

  (* TODO: may need AGB's encoding with setminus instead of union *)
  | Impl_R : forall (g d : env) (A B : LinProp),
              (A :: g U d) |- B ->
              (g U d) |- (A -o B)

  (* basically, if you can prove the assump A, then you can have the conclusion B *)
  | Impl_L : forall (g d1 d2 : env) (A B C : LinProp),
              (g U d1) |- A ->
              (B :: g U d2) |- C ->
              ((A -o B) :: g U d1 U d2) |- C

  | Times_R : forall (g d1 d2 : env) (A B : LinProp),
                (g U d1) |- A ->
                (g U d2) |- B ->
                (g U d1 U d2) |- (A ** B)

  | Times_L : forall (g d : env) (A B C : LinProp),
                (A :: B :: g U d) |- C ->
                ((A ** B) :: g U d) |- C

  | One_R : forall (g d : env),
              d = EmptyBag LinProp ->
              (g U d) |- One

  | One_L : forall (g d : env),
              (g U d) |- C ->
              (One :: g U d) |- C

  (* Additive connectives *)
  (* With = internal choice *)                                  
  | With_R : forall (g d : env) (A B : LinProp),
               (g U d) |- A ->
               (g U d) |- B ->
               (g U d) |- (A && B)

  | With_L1 : forall (g d : env) (A B C : LinProp),
                (A :: g U d) |- C ->
                ((A && B) :: g U d) |- C

  | With_L2 : forall (g d : env) (A B C : LinProp),
                (B :: g U d) |- C ->
                ((A && B) :: g U d) |- C

  | Top_R : forall (g d : env),
              (g U d) |- Top

  (* Plus = external choice *)
  | Plus_R1 : forall (g d : env) (A B : LinProp),
                (g U d) |- A ->
                (g U d) |- (A ++ B)

  | Plus_R2 : forall (g d : env) (A B : LinProp),
                (g U d) |- B ->
                (g U d) |- (A ++ B)

  | Plus_L : forall (g d : env) (A B C : LinProp),
               (A :: g U d) |- C ->
               (B :: g U d) |- C ->
               ((A ++ B) :: g U d) |- C

  | Zero_L : forall (g d : env) (C : LinProp),
               (Zero :: g U d) |- C

  (* Quantifiers: included in Coq *)

  (* Exponentials *)
  (* TODO: implication is included in Coq *)
  (* note the empty linear context *)
  | Bang_R : forall (g d : env) (A : LinProp),
               d = EmptyBag LinProp ->
               (g U d) |- A ->
               (g U d) |- !A

  (* move a linear factory to be a normal classical assumption *)
  | Bang_L : forall (g d : env) (A C : LinProp),
               ((A :: g) U d) |- C ->
               (g U (!A :: d)) |- C

  where "x |- y" := (LinProof x y).

(* Various other ILL axioms here *)

(* Multiset subtraction? TODO *)

(* End LinearLogic. *)
