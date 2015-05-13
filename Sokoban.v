Require Import LinearLogic.
Require Import BlocksWorld.

(* what's the point? how's this different from writing a program in haskell? I guess here, writing the rules is enough to enable you to play the game? *)

(* forward = pushing rule, backward = pulling rule

something can be clear and be a goal

up : location -> location

push (takes a direction function):

? p B _ ? 
|-
? _ p B ?

loc player (down pLoc) ** loc b1 pLoc ** clear (up pLoc)
|-
clear (down pLoc) ** loc player pLoc ** loc b1 (up pLoc) 

 *)

Definition loc : Type := prod nat nat.
(* Definition player : Type := nat. *)
(* Definition box : Type := nat. *)

Variable clear : loc -> LinProp.
Variable player : loc -> LinProp.
Variable box : loc -> LinProp.
Variable wall : loc -> LinProp.
Variable goal : loc -> LinProp.

Theorem level0 :
  {{clear (0,0)}} |- (clear (0,0)).
Proof.
  constructor. meq_clear.
Qed.

(* TODO: write a level to variable parser *)

Definition level1Str :=
"
-----
-pbg-
-----
".


Theorem level1 : forall (goalLoc : loc),
  goalLoc = (3,1) ->
  {{
    wall (0,2) ** wall (1,3) ** wall (2,3) ** wall (3,3) ** wall (4,3) ** wall (5,3) **
    wall (0,1) ** player (1,1) ** box (2,1) ** goal goalLoc ** clear goalLoc ** wall (4,1) **
    wall (0,0) ** wall (1,0) ** wall (2,0) ** wall (3,0) ** wall (4,0) ** wall (5,0) 
  }}
|- (box goalLoc ** Top). (* this is not so simple when there are multiple boxes and goals *)
Proof.
  intros. subst.

Admitted.

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
check for stuck states...

--------------
Player A has 


Goal:
Get Player B to like Player A


 *)
