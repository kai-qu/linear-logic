Require Import LinearLogic.
Require Import Coq.Strings.String.
Require Import Setoid.
Open Scope string_scope.

(* --------------- Setup *)

(* To allow setoid rewrites on multisets *)
Add Parametric Relation A : (multiset A) (@meq A)
 reflexivity proved by (@meq_refl A)
 symmetry proved by (@meq_sym A)
 transitivity proved by (@meq_trans A)
 as meq_rel.

Add Parametric Morphism A : (@munion A) with
  signature (@meq A) ==> (@meq A) ==> (@meq A) as munion_mor.
Proof. intros. Admitted.

(* TODO: Is it complaining that it doesn't know that
given: e ~ e'
goal: e |- g
it doesn't know that (e |- g) ~' (e' |- g)
for some other relation ~'? *)
(* Add Parametric Morphism A : (|-) with *)

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

Definition emptyBag := EmptyBag LinProp.

(* Lemmas about actions *)
Lemma getTable : forall (b : Block) (arm : Arm),
              {{ empty arm ** clear b ** table b }}
              |- (holds arm b).
Proof. 
  intros b arm.
  pose proof (get arm b b) as get.

  (* Set Printing All. *)
  (* Check Times_L. *)
  (* apply Times_L with (A := empty arm) (B := (clear b ** table b)). *)
  (* unfold inSet. *)
  (* unfold multiplicity. *)
  (* simpl. *)
  (* admit.                        (* eq_neq_LinProp *) *)
  
assert (get':
({{empty arm ** clear b}})
        |- (holds arm b ** (table b -o One) && (on b b -o clear b)) ->
(empty arm :: clear b :: emptyBag)
        |- (holds arm b ** (table b -o One) && (on b b -o clear b))).  admit. 
apply get' in get. clear get'.

assert (goal' :
 (empty arm :: clear b :: table b :: emptyBag) |- (holds arm b)
-> ({{empty arm ** clear b ** table b}}) |- (holds arm b)). admit. apply goal'. clear goal'.

  Check cut.
  apply cut with (d1 := empty arm :: clear b :: emptyBag)
                   (d2 := table b :: emptyBag)
                   (A := ((holds arm b) ** ((table b) -o One) && (on b b -o clear b))).
    unfold meq. intros. simpl. admit. (* need eq_neq_prop! *)

  apply get.
  (* TODO: state after cut is wrong. there's holds arm b ... :: empty arm *)
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

  (* TODO use impl_L here *)

  (* assert (forall A, {{A}} == (A :: emptyBag)). intros. apply munion_empty_right. *)

  (* (* TODO: add new morphism here? or relation? *) *)
  (* (* setoid_rewrite -> H. (* Fails *) *) *)

  (* assert (forall A, {{A}} = (A :: emptyBag)). admit. rewrite H0. *)

assert (H1:
   (holds arm b :: One :: emptyBag)
   |- (holds arm b)
->
   (holds arm b :: (table b -o One) :: table b :: emptyBag)
   |- (holds arm b)). admit. 

apply H1. 
(* clear H H0 H1. *)

(* apply One_L. *)
(*   unfold inSet. simpl. admit. *)
(* again, need to deal with multiplicity, setminus, and eq_neq_prop *)

assert (H:
 {{holds arm b}} |- (holds arm b)
->
   (holds arm b :: One :: emptyBag) |- (holds arm b)).
  admit.

apply H. clear H.
constructor.

unfold meq. intros. simpl. reflexivity.

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

(* Initial BlocksWorld state, goal, and proof transforming initial state into goal *)
Theorem SwapAB : forall (top bot other : Block) (arm : Arm),
                   {{ empty arm ** clear top ** on top bot ** table bot
                            ** table other ** clear other }}
                   |- (on bot top ** Top).
                  (* Top is supposed to be a sink for unused predicates, since 
                   g |- T for any g. *)
Proof.
  intros.
  
Admitted.


(* Possibly a checker for validity of states: TODO *)



(* Some automation: TODO *)

