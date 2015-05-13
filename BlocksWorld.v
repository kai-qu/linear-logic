Require Import LinearLogic.
Require Import Coq.Strings.String.
Require Import Setoid.
Require Import Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope string_scope.


Definition emptyBag := EmptyBag LinProp.

(* --------------- Setup *)

(* To allow setoid rewrites on multisets *)
Add Parametric Relation A : (multiset A) (@meq A)
 reflexivity proved by (@meq_refl A)
 symmetry proved by (@meq_sym A)
 transitivity proved by (@meq_trans A)
 as meq_rel.

Notation "P ~= Q" := (eqLinProp P Q) (at level 60, right associativity).

Lemma eqLinProp_refl : forall (A : LinProp), A ~= A.
Proof. 
  intros. unfold eqLinProp. induction A; simpl; try reflexivity; try (rewrite IHA1; rewrite IHA2; reflexivity); try assumption.
  symmetry. apply beq_nat_refl. admit.
Qed.

Lemma eqLinProp_sym : forall (A B : LinProp), A ~= B -> B ~= A.
Proof. 
  intros.
  unfold eqLinProp in *.
  induction A; induction B; simpl; try reflexivity; inversion H.

  symmetry in H1. apply beq_nat_eq in H1. rewrite H1. reflexivity.
  
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

Check LinProof.                 (* but this should be true *)
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
  setoid_rewrite H.
Admitted.  

Definition Block : Type := string. (* not nat, so it doesn't clash with Vars *)
Definition bl : Block := "b".
Definition Arm : Type := string. (* not nat, so it doesn't clash with Vars *)
Definition ar : Arm := "arm".
(* Also not modeling the table *)

(* Note that it's not a block datatype or arm datatype with internal state. Blocks and arms have no state. Their state is determined by the props holding for it in the environment. Could we model this differently? *)

(* ----------------------- *)

(* Props (describing states) *)

(* Here they are just axioms (?), but they could be "more provable axioms" if each block had a coordinate and size. So to prove (on x y), you would have to show that the locations and coordinates matches up. Or, you could write a function that computed on the locs and coords and returned a boolean. *)

(* Note that these are *linear logic propositions*, not *rules*, which are Coq propositions like (... --- ...) *)
(* Describes blocks *)
Variable on : Block -> Block -> LinProp.
Variable table : Block -> LinProp.
Variable clear : Block -> LinProp.
(* Describes robot arm *)
Variable holds : Arm -> Block -> LinProp.
Variable empty : Arm -> LinProp.

(* Axioms (valid actions) *)
(* Note these are rules (Coq propositions), not linear logic propositions *)

(* TODO: fix sequent notation so second arg doesn't need parens *)
Axiom get : forall (arm : Arm) (top bot : Block),
              {{ empty arm ** clear top }}
              |- (holds arm top **
                        ( (table top -o One) && (on top bot -o clear bot)) ).

Axiom put : forall (top bot : Block) (arm : Arm),
              {{ holds arm top }}
              |- (empty arm ** clear top **
                        (table top && (clear bot -o on top bot) )).

Axiom empty_eq : forall (a : Arm), eqLPC (empty a) (empty a) = true.
Axiom table_eq : forall (b : Block), eqLPC (table b) (table b) = true.
Axiom clear_eq : forall (b : Block), eqLPC (clear b) (clear b) = true.
Axiom on_eq : forall (b c : Block), eqLPC (on b c) (on b c) = true.
Axiom holds_eq : forall (a : Arm) (b : Block), eqLPC (holds a b) (holds a b) = true.

(* TODO prove and move elsewhere *)
Axiom times_assoc : forall A B C, (A ** (B ** C)) = ((A ** B) ** C).
Axiom times_comm : forall A B, (A ** B) = (B ** A).



(* Some automation *)

Tactic Notation "meq_clear" :=
    unfold meq;
    intros; unfold multiplicity; simpl;
    try reflexivity; try omega.

Tactic Notation "inSet_clear" :=
    unfold inSet; unfold multiplicity; simpl;
    repeat rewrite <- plus_n_O; try omega.

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

(* TODO: redo to work in sequent *)
Lemma unstick' :  forall (A B : LinProp) (env : env),
                   (A ** B) :: env = A :: B :: env. 
Proof.
  intros. 
Admitted.

(* ------------------------ *)

(* Lemmas about actions *)
Lemma getTable : forall (b : Block) (arm : Arm),
              {{ empty arm ** clear b ** table b }}
              |- (holds arm b).
Proof. 
  intros b arm.
  pose proof (get arm b b) as get.

  (* Set Printing All. *)
  Check Times_L.
  apply Times_L with (A := empty arm) (B := (clear b ** table b)).
  unfold inSet.
  unfold multiplicity.
  simpl.
  destruct (eq_neq_LinProp). omega. exfalso. apply n.
  unfold eqLinProp. rewrite times_assoc. simpl. rewrite empty_eq. rewrite clear_eq. rewrite table_eq. reflexivity.

  rewrite times_assoc.

  (* now to deal with setminus AND with clear b ** table b :( *)


assert (
   (empty arm
    :: (clear b) :: (table b)
       :: emptyBag) |- (holds arm b)
->
   (empty arm
    :: (clear b ** table b)
       :: {{empty arm ** clear b ** table b}} \
          (empty arm ** clear b ** table b)) |- (holds arm b)). admit. apply H. clear H.

  (* apply Times_L with (A := clear b) (B := table b). *)
  (*   unfold inSet.  *)

assert (get':
({{empty arm ** clear b}})
        |- (holds arm b ** (table b -o One) && (on b b -o clear b)) ->
(empty arm :: clear b :: emptyBag)
        |- (holds arm b ** (table b -o One) && (on b b -o clear b))).  admit. 
apply get' in get. clear get'.

  Check cut.
  apply cut with (d1 := empty arm :: clear b :: emptyBag)
                   (d2 := table b :: emptyBag)
                   (A := ((holds arm b) ** ((table b) -o One) && (on b b -o clear b))).
    unfold meq. intros. simpl. omega. 

  apply get.

  (* eapply Times_L. *)

  assert (H: 
            ((holds arm b) :: (table b -o One) && (on b b -o clear b)
    :: table b :: emptyBag) |- (holds arm b)
->
   ((holds arm b ** (table b -o One) && (on b b -o clear b))
    :: table b :: emptyBag) |- (holds arm b)). intros. (* eapply Times_L. *)
    admit.

    apply H. clear H.

    (* Check With_L1. *)
    (* apply With_L1 with (A := (table b -o One)) (B := (on b b -o clear b)). *)
    (*   unfold inSet. simpl. admit. *)
    (* TODO this will work but need to figure out how to deal with setMinus *)
    
  assert (H: 
   (holds arm b
    :: (table b -o One) 
       :: table b :: emptyBag) |- (holds arm b)
->
   (holds arm b
    :: (table b -o One) && (on b b -o clear b)
       :: table b :: emptyBag) |- (holds arm b)). admit.
  apply H. clear H.             (* holds arm and empty arm? *)
 
  clear get.

assert (H1:
   (holds arm b :: One :: emptyBag)
   |- (holds arm b)
->
   (holds arm b :: (table b -o One) :: table b :: emptyBag)
   |- (holds arm b)).

  intros.
  Check Impl_L.
  apply Impl_L with (d1 := table b :: emptyBag) (A := table b) (d2 := holds arm b :: emptyBag) (B := One).
    unfold inSet. simpl. remember (table b -o One) as imp. destruct (eq_neq_LinProp imp imp).
    omega. exfalso. apply n. unfold eqLinProp. subst. simpl. rewrite table_eq. reflexivity.
    (* TODO need two ltacs here!! *)

    unfold setMinus. simpl. unfold munion. simpl. unfold meq. intros. simpl.
    repeat rewrite <- plus_n_O.
    destruct (eq_neq_LinProp (table b -o One) a). omega. omega.

    constructor. unfold meq. intros. simpl. omega.
  
   admit. (* :: is "commutative" in H... may need meq and setoid rewrite *)

apply H1. 
(* clear H H0 H1. *)

apply One_L.
  unfold inSet. simpl.
  rewrite <- plus_n_O.
  Check (eq_neq_LinProp One One).
  SearchAbout sumbool.
  assert (eqLinProp One One). unfold eqLinProp. simpl. reflexivity.
    destruct (eq_neq_LinProp One One). omega.
    contradiction.

  assert (meq ((holds arm b :: One :: emptyBag) \ One) (holds arm b :: emptyBag)).
     unfold setMinus. unfold munion. unfold meq. simpl.
     intros. repeat rewrite <- plus_n_O. destruct (eq_neq_LinProp One a).
     omega. omega.

(* need a SETOID REWRITE with H *)
  assert (
 (holds arm b :: emptyBag) |- (holds arm b)
->
 ((holds arm b :: One :: emptyBag) \ One) |- (holds arm b)). admit.
  apply H0. clear H0.     

constructor. unfold meq. intros. simpl. omega.
Qed.

(* missing the fact that bot is on table, but it starts out being on the table anyway *)
Lemma puton : forall (top bot : Block) (arm : Arm),
                {{ holds arm top ** clear bot }}
                |- (empty arm ** clear top ** on top bot).
Proof. 
  intros.

Admitted.

Lemma putTable : forall (b : Block) (arm : Arm),
                   {{ holds arm b }}
                   |- (empty arm ** table b ** clear b).
Proof. 
  intros.

Admitted.

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

Lemma stick : forall (A B C : LinProp) (e : env),
                     ((A ** B) :: e) |- C ->
                     (A :: B :: e) |- C.
Proof.
  intros.

  (* induction H. *)
(* Print LinProof. *)
  
  inversion H; subst; clear H.
  unfold meq in *.              (* clearly true, since C must be A ** B here... *)
  admit.

  apply Impl_R. 

  admit.
Admitted.

Lemma eq_single : forall (A : LinProp),
                    {{A}} == (A :: emptyBag).
Proof. meq_clear. Qed.

(* Initial BlocksWorld state, goal, and proof transforming initial state into goal *)
Theorem SwapAB : forall (top bot other : Block) (arm : Arm),
                   {{ empty arm ** clear top ** on top bot ** table bot
                            ** table other ** clear other }}
                   |- (on bot top ** Top).
                  (* Top is supposed to be a sink for unused predicates, since 
                   g |- T for any g. *)
Proof.
  intros. rewrite eq_single. repeat apply unstick. apply stick.

(* pick up top *)
  eapply cut with (d1 := {{empty arm ** clear top}}) (d2 := on top bot :: table bot :: table other :: clear other :: emptyBag).
  meq_clear.

  apply get with (top := top) (bot := bot).
  apply unstick.

  apply With_L2 with (A := (table top -o One)) (B := (on top bot -o clear bot)).
    inSet_clear.
    eqterm_clear ((table top -o One) && (on top bot -o clear bot)) n.

  assert (
   ((on top bot -o clear bot)
    :: (holds arm top
           :: on top bot
              :: table bot :: table other :: clear other :: emptyBag))
==
   ((on top bot -o clear bot)
    :: (holds arm top
        :: (table top -o One) && (on top bot -o clear bot)
           :: on top bot
              :: table bot :: table other :: clear other :: emptyBag) \
       (table top -o One) && (on top bot -o clear bot))).
    setMinus_clear ((table top -o One) && (on top bot -o clear bot)) a.

    setoid_rewrite <- H. clear H.

    apply Impl_L with (d1 := {{on top bot}}) (d2 :=  (holds arm top ::
       table bot :: table other :: clear other :: emptyBag))
                                             (A := on top bot) (B := clear bot).

    inSet_clear. eqterm_clear (on top bot -o clear bot) n.
    meq_clear. destruct (eq_neq_LinProp (on top bot -o clear bot) a).
     simpl. rewrite <- minus_n_O. rewrite <- plus_n_O. omega. omega.

     constructor. meq_clear.

(* put it on the table *)
assert  ((clear bot
    :: holds arm top :: table bot :: table other :: clear other :: emptyBag) ==
   (holds arm top :: clear bot :: table bot :: table other :: clear other :: emptyBag)).
   meq_clear.

 setoid_rewrite H. clear H.

     eapply cut with (d1 := {{holds arm top}}) (d2 := clear bot :: table bot :: table other :: clear other :: emptyBag).
     meq_clear.

     eapply putTable.

(* pick up bottom from table *)
     repeat apply unstick.
     assert (
   (empty arm :: table bot :: clear bot
    :: clear top :: table top :: table other :: clear other :: emptyBag)
==
   (empty arm :: table top :: clear top
    :: clear bot :: table bot :: table other :: clear other :: emptyBag)).
     meq_clear.
     setoid_rewrite <- H. clear H.

     apply stick. apply stick.
 
     eapply cut with (d1 := {{empty arm ** clear bot ** table bot}}) (d2 := clear top :: table top :: table other :: clear other :: emptyBag).
     rewrite <- times_assoc. rewrite (times_comm (table bot) (clear bot)). rewrite times_assoc. meq_clear.

      apply getTable.

(* put it on top *)
      apply stick.

      eapply cut with (d1 := {{holds arm bot ** clear top}}) (d2 := table top :: table other :: clear other :: emptyBag). meq_clear.

      apply puton.

(* remove unused assumptions *)
      (* note: no assumptions here are contradictory *)
      repeat apply unstick.

      apply Times_R with (d2 := empty arm
    :: clear bot :: table top :: table other :: clear other :: emptyBag)
                           (d1 := {{on bot top}}).

      meq_clear.
      
      constructor. meq_clear.
      apply Top_R.
Qed.


(* Possibly a checker for validity of states: TODO *)

