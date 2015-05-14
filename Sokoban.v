Require Import LinearLogic.
Require Import EnvLemmas.
Require Import BlocksWorld.
Require Import Ascii String EqNat NArith.
Open Scope string_scope.

(* what's the point? how's this different from writing a program in haskell? I guess here, writing the rules is enough to enable you to play the game? *)
(* State: 

Given a freeform shape enclosed by walls 
with initial state locations of
- walls (immovable, cannot go on top)
- goals (immovable, can go on top)
- boxes (movable but changes location)
- one player (movable)

goal:
- all boxes on top of goals
- (walls won't have moved)
- (player can be anywhere)

Props:
clear location
box location
goal location
wall location
player location
loc (x,y)

location =
| loc : Object -> Coordinate -> Location

Object = Box Name | Player | Wall | Goal

Axioms:

let pLoc = (x,y)

moveUp : loc player pLoc ** clear (up pLoc) |- loc player (up pLoc)
moveDown : same
moveLeft : same
moveRight : same

--> what about chains of boxes?
--> uh, I'm not really using the other LL connectives...
--> what about the rest of the board?
--> doing the proof would be like working backward, or pulling the boxes...

pushUpOne : loc player pLoc ** loc box (up pLoc) ** clear (up up pLoc)
            |- loc player (up pLoc) ** loc box (up up pLoc)

pushUpBlocked : loc player pLoc ** loc box1 (up pLoc) ** loc box2 (up up pLoc)
            |- 

pushUpBlocked' : 
    you can push a chain of 2+ blocks forward one space if there is a free space after the block at the end. 
    to push a chain of 2+ blocks forward one space, 
    if the block in front can be pushed first...
    or, the chain of blocks got there if it...

    ? p B B ? ?

There's a difference between a SEQUENT and a LINE (RULE)

      clear (down pLoc) 
      |-
      loc player pLoc ** loc box1 (up pLoc) ** loc box2 (up up pLoc)

    

pushUp : loc player pLoc ** loc box (up pLoc) ** ...chaining... 
             note: chaining is also a problem for the 8-puzzle
          |- loc player (up pLoc) ** loc box (up up pLoc) ** ...chaining...
pushDown
pushLeft
pushRight

Initial state:
  clear (0,0) ** clear (0,1) **...** loc player pLoc ** loc box (up pLoc) ** ... loc goal gLoc ... ** loc wall wLoc1 **... |-

Final goal:
  (walls in same place) (goals in same place) ** 
  ... each box is on a different gLoc... TODO how to check this?? there are many ways for a box to be on a gLoc
  need to write a function: given a list of box locations and a list of glocs,
  - check that box locs <= gLocs
  - check that each box is on a unique gLoc

Proof search:

----
check for stuck states... *)

Definition loc : Type := prod nat nat.

Variable clear : loc -> LinProp.
Variable player : loc -> LinProp.
Variable box : loc -> LinProp.
Variable wall : loc -> LinProp.
Variable goal : loc -> LinProp.

(* forward = pushing rule, backward = pulling rule

something can be clear and be a goal

up : location -> location

push (takes a direction function):

? p B _ ? 
|-
? _ p B ?

? _ B p ? 
|-
? B p _ ?

loc player (down pLoc) ** loc b1 pLoc ** clear (up pLoc)
|-
clear (down pLoc) ** loc player pLoc ** loc b1 (up pLoc)  *)

Definition up (l : loc) := let (x,y) := l in (x, y + 1).
Definition down (l : loc) := let (x,y) := l in (x, y - 1).
Definition right (l : loc) := let (x,y) := l in (x + 1, y).
Definition left (l : loc) := let (x,y) := l in (x - 1, y).

(* hoare logic? *)
Axiom move : forall (c : loc) (dir : loc -> loc),
                 {{player (dir c)}}
                 |-
                 (clear (dir c) ** player c).

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


Theorem level0 :
  {{clear (0,0)}} |- (clear (0,0)).
Proof.
  constructor. meq_clear.
Qed.

(* TODO: write a level to variable parser, and variable to level *)

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

(* Approach modeled on Coq 2048 *)
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

