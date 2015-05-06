Require Import LinearLogic.
Require Import Coq.Strings.String.
Open Scope string_scope.

(* See Pfenning *)

Definition Block : Type := string. (* not nat, so it doesn't clash with Vars *)
Definition bl : Block := "b".
Definition Arm : Type := string. (* not nat, so it doesn't clash with Vars *)
Definition arm : Arm := "arm".
(* Also not modeling the table *)

(* Note that it's not a block datatype or arm datatype with internal state. Blocks and arms have no state. Their state is determined by the props holding for it in the environment. Could we model this differently? *)

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
(* Check {empty}. *)

Check ((EmptyBag LinProp) |- A).
Check (empty arm).
Check (clear bl).
Check ((empty arm) ** (clear bl)).
Check {{A ** B}}.
Check {{A ** B}} |- Top.

Axiom get : forall (b1 b2 : Block) (arm : Arm),
              {empty arm ** clear b2} |- Top.
              

(* Lemmas about actions *)


(* Possibly a checker for validity of states *)


(* Initial BlocksWorld state and goal *)


(* Some automation *)
(* Do we need the cut rule? *)


(* Proof transforming initial state into goal *)


