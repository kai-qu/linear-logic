(* From Wikipedia:

Sokoban (倉庫番 sōkoban?, warehouse keeper) is a type of transport puzzle, in which the player pushes boxes or crates around in a warehouse, trying to get them to storage locations. The puzzle is usually implemented as a video game.

That is, given a freeform shape with some initial state, which contains the locations of
- clear spaces (immovable, player can go on top)
- one player (movable, must start on a clear space)
- walls (immovable, player cannot go on top)
- goals (immovable, player can go on top)
- boxes (movable but change location, so player cannot go on top)

The player must achieve the goal of getting each box on top of a goal, finishing with all boxes on unique goals simultaneously.

The player can push boxes in one of four directions onto clear spaces. *)


(* Here, we use linear logic to model the initial state, goal, objects, and allowable action. Then we solve one very easy level of Sokoban.

Some notes on this file:

- Why use linear logic? Because it models state. If you move forward, you consume the fact that you were on the previous space. etc.
  Although I mostly use the (**) connective and none of the fancier ones...
- The axioms here in Coq are classical; so, the player can use them as many times as she wants.
- Why do this? How's this different from writing a program in haskell? The novelty is that here, writing the rules is enough to enable you to play the game!

- Sokoban is PSPACE-complete, so proof search will be slow. (It's not implemented here.)
- Applying rules forward (often using cut) equates to pushing the blocks. 
- Applying them backward, in proof assistant style, equates to pulling the blocks.

Some optimizations:

- More automation, so a move rule really does a move and doesn't require the environment to be manipulated 5 times to apply it, then apply the next rule.
- Pretty-printing (level -> environment parser, as well as environment -> level printer). I implemented a bit of it in the style of Coq 2048.
- Sokoban only allows the player to push one box at a time. One could generalize this to chains of boxes in a line.
- One could write a checker for stuck states, which do exist. *)


Require Import LinearLogic.
Require Import EnvLemmas.
Require Import BlocksWorld.
Require Import Ascii String EqNat NArith.
Open Scope string_scope.

Definition loc : Type := prod nat nat.

Variable clear : loc -> LinProp.
Variable player : loc -> LinProp.
Variable box : loc -> LinProp.
Variable wall : loc -> LinProp.
Variable goal : loc -> LinProp.


Definition up (l : loc) := let (x,y) := l in (x, y + 1).
Definition down (l : loc) := let (x,y) := l in (x, y - 1).
Definition right (l : loc) := let (x,y) := l in (x + 1, y).
Definition left (l : loc) := let (x,y) := l in (x - 1, y).

(* The player can either move onto a clear space, or push a box one space in one direction *)
Axiom move : forall (c : loc) (dir : loc -> loc),
                 {{player (dir c)}}
                 |-
                 (clear (dir c) ** player c).

(* Some diagrams.

Forward: Push to the right 
Backward: Pull to the left

 ? p B _ ? 
    |-
 ? _ p B ?

Forward: Push to the left
Backward: Pull to the left

 ? _ B p ? 
    |-
 ? B p _ ?              *)

Axiom pushUp : forall (center : loc),
  {{player (down center) ** box center ** clear (up center)}}
               |-
  (clear (down center) ** player center ** box (up center)).

Axiom pushDown : forall (center : loc),
  {{clear (down center) ** box center ** player (up center)}}
               |-
  (box (down center) ** player center ** clear (up center)).

Axiom pushRight : forall (center : loc),
  {{player (left center) ** box center ** clear (right center)}}
               |-
  (clear (left center) ** player center ** box (right center)).

Axiom pushLeft : forall (center : loc),
  {{clear (left center) ** box center ** player (right center)}}
               |-
  (box (left center) ** player center ** clear (right center)).

(* --------------------- *)

(* Solve an easy level of Sokoban (just pushes the block once to the right).
Note how many environment manipulations it takes. *)

Theorem level0 :
  {{clear (0,0)}} |- (clear (0,0)).
Proof.
  constructor. meq_clear.
Qed.

(* TODO: write a level to variable parser, and variable to level *)

(* Approach modeled on Coq 2048 *)
Definition nl := (String (ascii_of_nat 10) "")%string.
Definition test := ("hi" ++ nl ++ "hi")%string.
Definition level1Str :=
(nl ++ 
"-----" ++ nl ++
"-pbg-" ++ nl ++
"-----" ++ nl ++
"")%string.

Definition level1State goalLoc :=
  wall (0,2) ** wall (1,3) ** wall (2,3) ** wall (3,3) ** wall (4,3) ** wall (5,3) **
    wall (0,1) ** player (1,1) ** box (2,1) ** goal goalLoc ** clear goalLoc ** wall (4,1) **
    wall (0,0) ** wall (1,0) ** wall (2,0) ** wall (3,0) ** wall (4,0) ** wall (5,0).

Definition sokoban (l : Prop) (s : string) : Prop := l.

Notation "[Sokoban] a" := (sokoban _ a) (at level 10).

Definition toStr (s : LinProp) : string := level1Str.

Tactic Notation "display" constr(s) :=
  unfold toStr; unfold s;
  unfold nl; simpl;
  unfold ascii_of_nat; simpl; unfold ascii_of_pos; simpl.  

Theorem level1 : forall (goalLoc : loc) (state : LinProp),
  goalLoc = (3,1) ->
  state = level1State goalLoc ->  
  sokoban 
  ({{ state }} |- (box goalLoc ** Top))
  (toStr state).
Proof.
  intros. subst. display level1Str.
  unfold sokoban.

  (* TODO sokoban to sokoban ltac (re-draws board after tactic *)

  (* TODO automate this *)
  unfold level1State.

  (* find the relevant linprops that match the ones in pushRight; bring to front *)
assert (
((player (1, 1) ** 
      box (2, 1) ** clear (3, 1)) ** (goal (3,1) **
wall (0, 2) ** wall (1, 3) ** wall (2, 3) ** wall (3, 3) ** wall (4, 3) **
      wall (5, 3) ** wall (0, 1) ** 
      wall (4, 1) ** wall (0, 0) ** wall (1, 0) ** 
      wall (2, 0) ** wall (3, 0) ** wall (4, 0) ** 
      wall (5, 0)))
=
(wall (0, 2) ** wall (1, 3) ** wall (2, 3) ** wall (3, 3) ** wall (4, 3) **
      wall (5, 3) ** wall (0, 1) ** player (1, 1) ** 
      box (2, 1) ** goal (3, 1) ** clear (3, 1) ** 
      wall (4, 1) ** wall (0, 0) ** wall (1, 0) ** 
      wall (2, 0) ** wall (3, 0) ** wall (4, 0) ** 
      wall (5, 0))). (* by commutativity of (**) *) admit.
  
  rewrite <- H. clear H.

  (* separate into (_ ** _) :: (_ ** _) *)
  rewrite eq_single.
  apply unstick.

  (* then cut using the beginning and conclusion of pushRight *)
  eapply cut with (d1 := {{player (1, 1) ** box (2, 1) ** clear (3, 1)}})
  (d2 :=  {{goal (3, 1) ** wall (0, 2) ** wall (1, 3) ** wall (2, 3) **
        wall (3, 3) ** wall (4, 3) ** wall (5, 3) ** 
        wall (0, 1) ** wall (4, 1) ** wall (0, 0) ** 
        wall (1, 0) ** wall (2, 0) ** wall (3, 0) ** 
        wall (4, 0) ** wall (5, 0)}}). meq_clear.

  (* actually push *)
  (* rewrite times_comm. *)
  assert ((1,1) = left (2,1)). reflexivity.
  assert ((3,1) = right (2,1)). reflexivity.
  rewrite H. rewrite H0. clear H. clear H0.
  apply pushRight.

  (* get rid of the union, revert to ** so that the stage can be rendered *)
  simpl in *.
  
  repeat apply swap'.
  apply swap''.

(* finish by cutting and applying box (3,1) *)
(* need to move box out with :: *)

assert (
(clear (1, 1) **
      (player (2, 1) **
       (box (3, 1) **
        (goal (3, 1) ** wall (0, 2) ** wall (1, 3) ** wall (2, 3) **
         wall (3, 3) ** wall (4, 3) ** wall (5, 3) ** 
         wall (0, 1) ** wall (4, 1) ** wall (0, 0) ** 
         wall (1, 0) ** wall (2, 0) ** wall (3, 0) ** 
         wall (4, 0) ** wall (5, 0))))) =
(box (3, 1) **
      (player (2, 1) **
       (clear (1, 1) **
        (goal (3, 1) ** wall (0, 2) ** wall (1, 3) ** wall (2, 3) **
         wall (3, 3) ** wall (4, 3) ** wall (5, 3) ** 
         wall (0, 1) ** wall (4, 1) ** wall (0, 0) ** 
         wall (1, 0) ** wall (2, 0) ** wall (3, 0) ** 
         wall (4, 0) ** wall (5, 0)))))). (* by ** comm and assoc *) admit.
rewrite H. clear H.

rewrite eq_single.
apply unstick.
  
  eapply Times_R with (d1 := {{box (3,1)}}) (d2 := {{ (player (2, 1) **
        (clear (1, 1) **
         (goal (3, 1) ** wall (0, 2) ** wall (1, 3) ** wall (2, 3) **
          wall (3, 3) ** wall (4, 3) ** wall (5, 3) ** 
          wall (0, 1) ** wall (4, 1) ** wall (0, 0) ** 
          wall (1, 0) ** wall (2, 0) ** wall (3, 0) ** 
          wall (4, 0) ** wall (5, 0))))  }}). meq_clear.

  constructor. meq_clear.
  apply Top_R.

  (* TODO: embed this tactic in something that manipulates the sokoban (with image) *)
Qed.


Definition level2Str := 
"
----------
-        -
-p   b   -
-    -   -
-    g   -
-        -
----------
". 

(* TODO: define this and solve it! (push block to the left, then down and to the right *)

