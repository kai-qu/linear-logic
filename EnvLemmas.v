(* Some relations to define multiset equivalence and allow setoid rewrites.

Lemmas about manipulating the environment, plus some tactics for automatically discharging environment proofs. *)

Require Import LinearLogic.
Require Import Setoid.
Require Import Omega.
Require Import String.

(* Copied from BlockWorld *)
Definition Block : Type := string.
Definition Arm : Type := string.

Variable on : Block -> Block -> LinProp.
Variable table : Block -> LinProp.
Variable clear : Block -> LinProp.
(* Describes robot arm *)
Variable holds : Arm -> Block -> LinProp.
Variable empty : Arm -> LinProp.

Axiom empty_eq : forall (a : Arm), eqLPC (empty a) (empty a) = true.
Axiom table_eq : forall (b : Block), eqLPC (table b) (table b) = true.
Axiom clear_eq : forall (b : Block), eqLPC (clear b) (clear b) = true.
Axiom on_eq : forall (b c : Block), eqLPC (on b c) (on b c) = true.
Axiom holds_eq : forall (a : Arm) (b : Block), eqLPC (holds a b) (holds a b) = true.

(* ---------------------------- *)

Definition emptyBag := EmptyBag LinProp.

(* To allow setoid rewrites on multisets *)
Add Parametric Relation A : (multiset A) (@meq A)
 reflexivity proved by (@meq_refl A)
 symmetry proved by (@meq_sym A)
 transitivity proved by (@meq_trans A)
 as meq_rel.

Notation "P ~= Q" := (eqLinProp P Q) (at level 60, right associativity).

Lemma eqLinProp_refl : forall (A : LinProp), A ~= A.
Proof. 
  intros. unfold eqLinProp. induction A; simpl; try reflexivity;
                            try (rewrite IHA1; rewrite IHA2; reflexivity); try assumption.
  symmetry. apply EqNat.beq_nat_refl.  admit.
Qed.

Lemma eqLinProp_sym : forall (A B : LinProp), A ~= B -> B ~= A.
Proof. 
  intros.
  unfold eqLinProp in *.
  induction A; induction B; simpl; try reflexivity; inversion H.

  symmetry in H1. apply EqNat.beq_nat_eq in H1. rewrite H1. reflexivity.
  rewrite H1. admit.

Admitted.

Lemma eqLinProp_trans : forall (A B C : LinProp), A ~= B -> B ~= C -> A ~= C.
Proof. 
Admitted.

Add Parametric Relation : (LinProp) (eqLinProp)
 reflexivity proved by (eqLinProp_refl)
 symmetry proved by (eqLinProp_sym)
 transitivity proved by (eqLinProp_trans)
 as eqLinProp_rel.

Add Morphism LinProof with
  signature (@meq LinProp) ==> eqLinProp ==> (Basics.flip Basics.impl)
      as seq_mor.
Proof.
  intros.
Admitted.

Lemma setoid_rewrite_test_sequent : forall (s: multiset LinProp),
                              meq s emptyBag ->
                                   s |- Top.
Proof.
  intros.
  setoid_rewrite H.             (* works *)
Admitted.  

(* --------------- *)

(* Some automation for environments *)

Tactic Notation "meq_clear" :=
    unfold meq;
    intros; unfold multiplicity; simpl;
    try reflexivity; try omega.

Tactic Notation "inSet_clear" :=
    unfold inSet; unfold multiplicity; simpl;
    repeat rewrite <- plus_n_O; try omega.

(* must call with ident "n" *)
Tactic Notation "eqterm_clear" constr(t) ident(n) :=
  destruct (eq_neq_LinProp t t);
  [ omega |
    exfalso; apply n; try apply eqLinProp_refl;
    unfold eqLinProp; simpl;
    try rewrite table_eq; try rewrite on_eq;
    try rewrite clear_eq; try rewrite holds_eq; try rewrite empty_eq;
    reflexivity].

Tactic Notation "setMinus_clear" constr(t) ident(a) :=
    unfold setMinus; simpl; unfold munion; simpl; meq_clear; 
    repeat rewrite <- plus_n_O;
    destruct (eq_neq_LinProp t a);
    omega; omega.

(* -------------- *)

Lemma unstick : forall (A B C : LinProp) (e : env),
                     (A :: B :: e) |- C ->
                     ((A ** B) :: e) |- C.
Proof.
  intros. 
  apply Times_L with (A := A) (B := B).
  inSet_clear. destruct eq_neq_LinProp. omega. exfalso. apply n. apply eqLinProp_refl.
  
  assert ((A :: B :: ((A ** B) :: e) \ (A ** B)) == (A :: B :: e)).
  unfold setMinus. meq_clear. destruct (eq_neq_LinProp (A ** B) a). omega. omega.

  setoid_rewrite H0. assumption.
Qed.

(* TODO: redo to work in sequent *)
Lemma unstick' :  forall (A B : LinProp) (env : env),
                   (A ** B) :: env = A :: B :: env. 
Proof.
  intros. 
Admitted.

Lemma stick : forall (A B C : LinProp) (e : env),
                     ((A ** B) :: e) |- C ->
                     (A :: B :: e) |- C.
Proof.
  intros.
  
  inversion H; subst; clear H.
  unfold meq in *.              (* clearly true, since C must be A ** B here... *)
  admit.

  apply Impl_R. 

  admit.
Admitted.

Lemma single_notation : forall (A B : LinProp), ({{A}} U {{B}}) == (A :: B :: emptyBag).
Proof. meq_clear. Qed.

Lemma swap : forall (A B C G : LinProp) (e : env),
               ((A :: (B ** C) :: e) |- G)
               ->
               (((A ** B) :: C :: e) |- G).
Proof.
  intros.

  apply Times_L with (A := A) (B := B). inSet_clear.
  eqterm_clear (A ** B) n.

  assert ((A :: B :: ((A ** B) :: C :: e) \ (A ** B)) == (A :: B :: C :: e)).
  meq_clear. setMinus_clear (A ** B) a. rewrite H0. clear H0.

  inversion H; subst. admit. admit. admit. admit.
  (* why is this so hard to prove? it is true *)
  
Admitted.

Lemma swap' : forall (A B C G : LinProp),
               ((A :: {{B ** C}}) |- G)
               ->
               (((A ** B) :: {{C}}) |- G).
Proof.
  intros.
  assert (forall P, {{P}} = P :: emptyBag). unfold singleton. unfold munion.
  unfold SingletonBag. intros. simpl. f_equal. admit. (* functional_extensionality. *)
  pose proof H0.
  specialize (H0 C).
  rewrite H0.
  apply swap.
  specialize (H1 (B ** C)).
  rewrite <- H1.
  apply H.
Qed.

Lemma swap'' : forall (A C G : LinProp),
               ({{A ** C}} |- G)
               ->
               (A :: {{C}}) |- G.
Proof.
  intros.
Admitted.

Lemma eq_single : forall (A : LinProp),
                    {{A}} == (A :: emptyBag).
Proof. meq_clear. Qed.