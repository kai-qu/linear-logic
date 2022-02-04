(* For the blocks world example in Power/Webster: defines primitives, defines actions of robot arms, and defines 3 sub-lemmas. 

Proves the main example:

 B
 A  C
-------

can be transformed into 


 A
 B  C
-------

(where the second stack of 2 blocks is at a different place on the table) *)

Require Import LinearLogic.
Require Import EnvLemmas.
Require Import Coq.Strings.String.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope string_scope.


Definition Block : Type := string.
Definition Arm : Type := string.
(* Also not modeling the table *)

(* Note that it's not a block datatype or arm datatype with internal state. Blocks and arms have no state. Their state is determined by the props holding for it in the environment. Could we model this differently? *)

(* ----------------------- *)

(* Props (describing states) *)

(* Here they are just axioms (?), but they could be "more provable axioms" if each block had a coordinate and size. So to prove (on x y), you would have to show that the locations and coordinates matches up. Or, you could write a function that computed on the locs and coords and returned a boolean. *)

(* Note that these are *linear logic propositions*, not *rules*, which are Coq propositions like (... --- ...) *)
(* Describes blocks *)
Parameter on : Block -> Block -> LinProp.
Parameter table : Block -> LinProp.
Parameter clear : Block -> LinProp.
(* Describes robot arm *)
Parameter holds : Arm -> Block -> LinProp.
Parameter empty : Arm -> LinProp.

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

(* ------------------------ *)

(* Lemmas about actions *)

(* getTable is long and messy -- first axiom I proved, so no automation *)
Lemma getTable : forall (b : Block) (arm : Arm),
              {{ empty arm ** clear b ** table b }}
              |- (holds arm b).
Proof. 
  intros b arm.
  pose proof (get arm b b) as get.

  apply Times_L with (A := empty arm) (B := (clear b ** table b)).
  unfold inSet.
  unfold multiplicity.
  simpl.
  destruct (eq_neq_LinProp). lia. exfalso. apply n.
  unfold eqLinProp. rewrite times_assoc. simpl. rewrite empty_eq. rewrite clear_eq. rewrite table_eq. reflexivity.

  rewrite times_assoc.


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

  apply cut with (d1 := empty arm :: clear b :: emptyBag)
                   (d2 := table b :: emptyBag)
                   (A := ((holds arm b) ** ((table b) -o One) && (on b b -o clear b))).
    unfold meq. intros. simpl. lia. 

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
  apply Impl_L with (d1 := table b :: emptyBag) (A := table b) (d2 := holds arm b :: emptyBag) (B := One).
    unfold inSet. simpl. remember (table b -o One) as imp. destruct (eq_neq_LinProp imp imp).
    lia. exfalso. apply n. unfold eqLinProp. subst. simpl. rewrite table_eq. reflexivity.
    (* TODO need two ltacs here!! *)

    unfold setMinus. simpl. unfold munion. simpl. unfold meq. intros. simpl.
    repeat rewrite <- plus_n_O.
    destruct (eq_neq_LinProp (table b -o One) a). lia. lia.

    constructor. unfold meq. intros. simpl. lia.
  
   admit. (* :: is "commutative" in H... may need meq and setoid rewrite *)

apply H1. 
(* clear H H0 H1. *)

apply One_L.
  unfold inSet. simpl.
  rewrite <- plus_n_O.
  assert (eqLinProp One One). unfold eqLinProp. simpl. reflexivity.
    destruct (eq_neq_LinProp One One). lia.
    contradiction.

  assert (meq ((holds arm b :: One :: emptyBag) \ One) (holds arm b :: emptyBag)).
     unfold setMinus. unfold munion. unfold meq. simpl.
     intros. repeat rewrite <- plus_n_O. destruct (eq_neq_LinProp One a).
     lia. lia.

(* need a SETOID REWRITE with H *)
  assert (
 (holds arm b :: emptyBag) |- (holds arm b)
->
 ((holds arm b :: One :: emptyBag) \ One) |- (holds arm b)). admit.
  apply H0. clear H0.     

constructor. unfold meq. intros. simpl. lia.
Admitted.

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

(* -------------- *)

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
     simpl. lia. lia.

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
