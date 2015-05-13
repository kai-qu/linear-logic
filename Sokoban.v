Require Import LinearLogic.

(* what's the point? *)
(* State: 

Given a 10x10 grid
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

pushUpOne :

pushUpBlocked : 

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
