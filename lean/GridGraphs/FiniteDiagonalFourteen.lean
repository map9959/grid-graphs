import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for fourteen rows

This file records the row-mask construction
`[2, 16382, 14046, 7926, 7094, 7094, 6838, 7094, 7094, 7862, 6070,
7606, 8190, 4098]`. Connectivity of its U-U dual is certified by explicit
parent, rank, and crossed primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The mask in row `r` of the fourteen-by-fourteen construction. -/
def finiteU14Mask : Nat → Nat
  | 0 => 2 | 1 => 16382 | 2 => 14046 | 3 => 7926
  | 4 => 7094 | 5 => 7094 | 6 => 6838 | 7 => 7094
  | 8 => 7094 | 9 => 7862 | 10 => 6070 | 11 => 7606
  | 12 => 8190 | 13 => 4098 | _ => 0

private def finiteU14Selected (v : GridVertex 14 14) : Bool :=
  match v.1.val with
  | 0 => v.2.val == 1
  | 1 => 1 ≤ v.2.val
  | 2 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 3 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 11 || v.2.val == 12
  | 4 | 5 | 7 | 8 => v.2.val == 1 || v.2.val == 2 ||
      v.2.val == 4 || v.2.val == 5 || v.2.val == 7 ||
      v.2.val == 8 || v.2.val == 9 || v.2.val == 11 || v.2.val == 12
  | 6 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 9 ||
      v.2.val == 11 || v.2.val == 12
  | 9 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 9 ||
      v.2.val == 10 || v.2.val == 11 || v.2.val == 12
  | 10 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 8 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 12
  | 11 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 8 ||
      v.2.val == 10 || v.2.val == 11 || v.2.val == 12
  | 12 => 1 ≤ v.2.val && v.2.val ≤ 12
  | 13 => v.2.val == 1 || v.2.val == 12
  | _ => false

/-- The selected vertices with the fourteen specified row masks. -/
def finiteU14 : Finset (GridVertex 14 14) :=
  Finset.univ.filter fun v => finiteU14Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU14Parent : GridFace 14 14 → GridFace 14 14
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 0 1 | 0, 1 => .cell 1 1 | 0, 2 => .cell 1 2
      | 0, 3 => .cell 1 3 | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7 | 0, 8 => .cell 1 8
      | 0, 9 => .cell 1 9 | 0, 10 => .cell 1 10 | 0, 11 => .cell 1 11
      | 0, 12 => .cell 1 12
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 1 2 | 1, 2 => .cell 1 3
      | 1, 3 => .cell 2 3 | 1, 4 => .cell 1 3 | 1, 5 => .cell 1 6
      | 1, 6 => .cell 2 6 | 1, 7 => .cell 1 6 | 1, 8 => .cell 1 9
      | 1, 9 => .cell 2 9 | 1, 10 => .cell 1 9 | 1, 11 => .cell 1 12
      | 1, 12 => .out
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 1 1 | 2, 2 => .cell 1 2
      | 2, 3 => .cell 2 4 | 2, 4 => .cell 3 4 | 2, 5 => .cell 2 6
      | 2, 6 => .cell 3 6 | 2, 7 => .cell 2 6 | 2, 8 => .cell 2 9
      | 2, 9 => .cell 2 10 | 2, 10 => .cell 3 10 | 2, 11 => .cell 2 12
      | 2, 12 => .cell 1 12
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 2 1 | 3, 2 => .cell 3 1
      | 3, 3 => .cell 3 4 | 3, 4 => .cell 3 5 | 3, 5 => .cell 2 5
      | 3, 6 => .cell 3 7 | 3, 7 => .cell 4 7 | 3, 8 => .cell 3 9
      | 3, 9 => .cell 2 9 | 3, 10 => .cell 3 11 | 3, 11 => .cell 2 11
      | 3, 12 => .cell 3 11
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 3 1 | 4, 2 => .cell 4 1
      | 4, 3 => .cell 4 4 | 4, 4 => .cell 3 4 | 4, 5 => .cell 4 4
      | 4, 6 => .cell 4 7 | 4, 7 => .cell 4 8 | 4, 8 => .cell 3 8
      | 4, 9 => .cell 4 8 | 4, 10 => .cell 4 11 | 4, 11 => .cell 3 11
      | 4, 12 => .cell 4 11
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 4 1 | 5, 2 => .cell 5 1
      | 5, 3 => .cell 5 4 | 5, 4 => .cell 4 4 | 5, 5 => .cell 5 4
      | 5, 6 => .cell 5 7 | 5, 7 => .cell 4 7 | 5, 8 => .cell 4 8
      | 5, 9 => .cell 5 8 | 5, 10 => .cell 5 11 | 5, 11 => .cell 4 11
      | 5, 12 => .cell 5 11
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 5 1 | 6, 2 => .cell 6 1
      | 6, 3 => .cell 6 4 | 6, 4 => .cell 5 4 | 6, 5 => .cell 6 4
      | 6, 6 => .cell 6 7 | 6, 7 => .cell 7 7 | 6, 8 => .cell 7 8
      | 6, 9 => .cell 6 8 | 6, 10 => .cell 6 11 | 6, 11 => .cell 5 11
      | 6, 12 => .cell 6 11
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 6 1 | 7, 2 => .cell 7 1
      | 7, 3 => .cell 7 4 | 7, 4 => .cell 6 4 | 7, 5 => .cell 7 4
      | 7, 6 => .cell 7 7 | 7, 7 => .cell 7 8 | 7, 8 => .cell 8 8
      | 7, 9 => .cell 7 8 | 7, 10 => .cell 7 11 | 7, 11 => .cell 6 11
      | 7, 12 => .cell 7 11
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 7 1 | 8, 2 => .cell 8 1
      | 8, 3 => .cell 8 4 | 8, 4 => .cell 7 4 | 8, 5 => .cell 8 4
      | 8, 6 => .cell 8 7 | 8, 7 => .cell 7 7 | 8, 8 => .cell 8 9
      | 8, 9 => .cell 9 9 | 8, 10 => .cell 8 11 | 8, 11 => .cell 7 11
      | 8, 12 => .cell 8 11
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 8 1 | 9, 2 => .cell 9 1
      | 9, 3 => .cell 9 4 | 9, 4 => .cell 8 4 | 9, 5 => .cell 9 4
      | 9, 6 => .cell 9 7 | 9, 7 => .cell 10 7 | 9, 8 => .cell 9 9
      | 9, 9 => .cell 9 10 | 9, 10 => .cell 8 10 | 9, 11 => .cell 8 11
      | 9, 12 => .cell 9 11
      | 10, 0 => .cell 10 1 | 10, 1 => .cell 9 1 | 10, 2 => .cell 10 1
      | 10, 3 => .cell 10 4 | 10, 4 => .cell 9 4 | 10, 5 => .cell 10 4
      | 10, 6 => .cell 10 7 | 10, 7 => .cell 10 8 | 10, 8 => .cell 9 8
      | 10, 9 => .cell 9 9 | 10, 10 => .cell 10 9 | 10, 11 => .cell 11 11
      | 10, 12 => .cell 10 11
      | 11, 0 => .cell 11 1 | 11, 1 => .cell 10 1 | 11, 2 => .cell 11 1
      | 11, 3 => .cell 11 4 | 11, 4 => .cell 10 4 | 11, 5 => .cell 11 4
      | 11, 6 => .cell 11 7 | 11, 7 => .cell 10 7 | 11, 8 => .cell 11 7
      | 11, 9 => .cell 11 10 | 11, 10 => .cell 10 10 | 11, 11 => .cell 11 10
      | 11, 12 => .cell 11 11
      | 12, 0 => .cell 12 1 | 12, 1 => .cell 11 1 | 12, 2 => .cell 11 2
      | 12, 3 => .cell 11 3 | 12, 4 => .cell 11 4 | 12, 5 => .cell 11 5
      | 12, 6 => .cell 11 6 | 12, 7 => .cell 11 7 | 12, 8 => .cell 11 8
      | 12, 9 => .cell 11 9 | 12, 10 => .cell 11 10 | 12, 11 => .cell 11 11
      | 12, 12 => .cell 12 11
      | _, _ => .out

/-- Depths in `finiteU14Parent`, with the outside face at rank zero. -/
def finiteU14Rank : GridFace 14 14 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 24 | 0, 1 => 23 | 0, 2 => 22 | 0, 3 => 21 | 0, 4 => 22
      | 0, 5 => 17 | 0, 6 => 16 | 0, 7 => 17 | 0, 8 => 10 | 0, 9 => 9
      | 0, 10 => 10 | 0, 11 => 3 | 0, 12 => 2
      | 1, 0 => 23 | 1, 1 => 22 | 1, 2 => 21 | 1, 3 => 20 | 1, 4 => 21
      | 1, 5 => 16 | 1, 6 => 15 | 1, 7 => 16 | 1, 8 => 9 | 1, 9 => 8
      | 1, 10 => 9 | 1, 11 => 2 | 1, 12 => 1
      | 2, 0 => 24 | 2, 1 => 23 | 2, 2 => 22 | 2, 3 => 19 | 2, 4 => 18
      | 2, 5 => 15 | 2, 6 => 14 | 2, 7 => 15 | 2, 8 => 8 | 2, 9 => 7
      | 2, 10 => 6 | 2, 11 => 3 | 2, 12 => 2
      | 3, 0 => 25 | 3, 1 => 24 | 3, 2 => 25 | 3, 3 => 18 | 3, 4 => 17
      | 3, 5 => 16 | 3, 6 => 13 | 3, 7 => 12 | 3, 8 => 9 | 3, 9 => 8
      | 3, 10 => 5 | 3, 11 => 4 | 3, 12 => 5
      | 4, 0 => 26 | 4, 1 => 25 | 4, 2 => 26 | 4, 3 => 19 | 4, 4 => 18
      | 4, 5 => 19 | 4, 6 => 12 | 4, 7 => 11 | 4, 8 => 10 | 4, 9 => 11
      | 4, 10 => 6 | 4, 11 => 5 | 4, 12 => 6
      | 5, 0 => 27 | 5, 1 => 26 | 5, 2 => 27 | 5, 3 => 20 | 5, 4 => 19
      | 5, 5 => 20 | 5, 6 => 13 | 5, 7 => 12 | 5, 8 => 11 | 5, 9 => 12
      | 5, 10 => 7 | 5, 11 => 6 | 5, 12 => 7
      | 6, 0 => 28 | 6, 1 => 27 | 6, 2 => 28 | 6, 3 => 21 | 6, 4 => 20
      | 6, 5 => 21 | 6, 6 => 18 | 6, 7 => 17 | 6, 8 => 16 | 6, 9 => 17
      | 6, 10 => 8 | 6, 11 => 7 | 6, 12 => 8
      | 7, 0 => 29 | 7, 1 => 28 | 7, 2 => 29 | 7, 3 => 22 | 7, 4 => 21
      | 7, 5 => 22 | 7, 6 => 17 | 7, 7 => 16 | 7, 8 => 15 | 7, 9 => 16
      | 7, 10 => 9 | 7, 11 => 8 | 7, 12 => 9
      | 8, 0 => 30 | 8, 1 => 29 | 8, 2 => 30 | 8, 3 => 23 | 8, 4 => 22
      | 8, 5 => 23 | 8, 6 => 18 | 8, 7 => 17 | 8, 8 => 14 | 8, 9 => 13
      | 8, 10 => 10 | 8, 11 => 9 | 8, 12 => 10
      | 9, 0 => 31 | 9, 1 => 30 | 9, 2 => 31 | 9, 3 => 24 | 9, 4 => 23
      | 9, 5 => 24 | 9, 6 => 17 | 9, 7 => 16 | 9, 8 => 13 | 9, 9 => 12
      | 9, 10 => 11 | 9, 11 => 10 | 9, 12 => 11
      | 10, 0 => 32 | 10, 1 => 31 | 10, 2 => 32 | 10, 3 => 25 | 10, 4 => 24
      | 10, 5 => 25 | 10, 6 => 16 | 10, 7 => 15 | 10, 8 => 14 | 10, 9 => 13
      | 10, 10 => 14 | 10, 11 => 17 | 10, 12 => 18
      | 11, 0 => 33 | 11, 1 => 32 | 11, 2 => 33 | 11, 3 => 26 | 11, 4 => 25
      | 11, 5 => 26 | 11, 6 => 17 | 11, 7 => 16 | 11, 8 => 17 | 11, 9 => 16
      | 11, 10 => 15 | 11, 11 => 16 | 11, 12 => 17
      | 12, 0 => 34 | 12, 1 => 33 | 12, 2 => 34 | 12, 3 => 27 | 12, 4 => 26
      | 12, 5 => 27 | 12, 6 => 18 | 12, 7 => 17 | 12, 8 => 18 | 12, 9 => 17
      | 12, 10 => 16 | 12, 11 => 17 | 12, 12 => 18
      | _, _ => 0

private inductive FiniteU14PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 14 14)
  | vertical (edge : VerticalGridEdge 14 14)

private def FiniteU14PrimalEdge.primalEndpoints :
    FiniteU14PrimalEdge → GridVertex 14 14 × GridVertex 14 14
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU14PrimalEdge.dualEndpoints :
    FiniteU14PrimalEdge → GridFace 14 14 × GridFace 14 14
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU14ParentEdge : GridFace 14 14 → FiniteU14PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .vertical ⟨0, 1⟩ | 0, 1 => .horizontal ⟨1, 1⟩
      | 0, 2 => .horizontal ⟨1, 2⟩ | 0, 3 => .horizontal ⟨1, 3⟩
      | 0, 4 => .horizontal ⟨1, 4⟩ | 0, 5 => .horizontal ⟨1, 5⟩
      | 0, 6 => .horizontal ⟨1, 6⟩ | 0, 7 => .horizontal ⟨1, 7⟩
      | 0, 8 => .horizontal ⟨1, 8⟩ | 0, 9 => .horizontal ⟨1, 9⟩
      | 0, 10 => .horizontal ⟨1, 10⟩ | 0, 11 => .horizontal ⟨1, 11⟩
      | 0, 12 => .horizontal ⟨1, 12⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .vertical ⟨1, 2⟩
      | 1, 2 => .vertical ⟨1, 3⟩ | 1, 3 => .horizontal ⟨2, 3⟩
      | 1, 4 => .vertical ⟨1, 4⟩ | 1, 5 => .vertical ⟨1, 6⟩
      | 1, 6 => .horizontal ⟨2, 6⟩ | 1, 7 => .vertical ⟨1, 7⟩
      | 1, 8 => .vertical ⟨1, 9⟩ | 1, 9 => .horizontal ⟨2, 9⟩
      | 1, 10 => .vertical ⟨1, 10⟩ | 1, 11 => .vertical ⟨1, 12⟩
      | 1, 12 => .vertical ⟨1, 13⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .horizontal ⟨2, 1⟩
      | 2, 2 => .horizontal ⟨2, 2⟩ | 2, 3 => .vertical ⟨2, 4⟩
      | 2, 4 => .horizontal ⟨3, 4⟩ | 2, 5 => .vertical ⟨2, 6⟩
      | 2, 6 => .horizontal ⟨3, 6⟩ | 2, 7 => .vertical ⟨2, 7⟩
      | 2, 8 => .vertical ⟨2, 9⟩ | 2, 9 => .vertical ⟨2, 10⟩
      | 2, 10 => .horizontal ⟨3, 10⟩ | 2, 11 => .vertical ⟨2, 12⟩
      | 2, 12 => .horizontal ⟨2, 12⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨3, 1⟩
      | 3, 2 => .vertical ⟨3, 2⟩ | 3, 3 => .vertical ⟨3, 4⟩
      | 3, 4 => .vertical ⟨3, 5⟩ | 3, 5 => .horizontal ⟨3, 5⟩
      | 3, 6 => .vertical ⟨3, 7⟩ | 3, 7 => .horizontal ⟨4, 7⟩
      | 3, 8 => .vertical ⟨3, 9⟩ | 3, 9 => .horizontal ⟨3, 9⟩
      | 3, 10 => .vertical ⟨3, 11⟩ | 3, 11 => .horizontal ⟨3, 11⟩
      | 3, 12 => .vertical ⟨3, 12⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .horizontal ⟨4, 1⟩
      | 4, 2 => .vertical ⟨4, 2⟩ | 4, 3 => .vertical ⟨4, 4⟩
      | 4, 4 => .horizontal ⟨4, 4⟩ | 4, 5 => .vertical ⟨4, 5⟩
      | 4, 6 => .vertical ⟨4, 7⟩ | 4, 7 => .vertical ⟨4, 8⟩
      | 4, 8 => .horizontal ⟨4, 8⟩ | 4, 9 => .vertical ⟨4, 9⟩
      | 4, 10 => .vertical ⟨4, 11⟩ | 4, 11 => .horizontal ⟨4, 11⟩
      | 4, 12 => .vertical ⟨4, 12⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .horizontal ⟨5, 1⟩
      | 5, 2 => .vertical ⟨5, 2⟩ | 5, 3 => .vertical ⟨5, 4⟩
      | 5, 4 => .horizontal ⟨5, 4⟩ | 5, 5 => .vertical ⟨5, 5⟩
      | 5, 6 => .vertical ⟨5, 7⟩ | 5, 7 => .horizontal ⟨5, 7⟩
      | 5, 8 => .horizontal ⟨5, 8⟩ | 5, 9 => .vertical ⟨5, 9⟩
      | 5, 10 => .vertical ⟨5, 11⟩ | 5, 11 => .horizontal ⟨5, 11⟩
      | 5, 12 => .vertical ⟨5, 12⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨6, 1⟩
      | 6, 2 => .vertical ⟨6, 2⟩ | 6, 3 => .vertical ⟨6, 4⟩
      | 6, 4 => .horizontal ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 5⟩
      | 6, 6 => .vertical ⟨6, 7⟩ | 6, 7 => .horizontal ⟨7, 7⟩
      | 6, 8 => .horizontal ⟨7, 8⟩ | 6, 9 => .vertical ⟨6, 9⟩
      | 6, 10 => .vertical ⟨6, 11⟩ | 6, 11 => .horizontal ⟨6, 11⟩
      | 6, 12 => .vertical ⟨6, 12⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨7, 1⟩
      | 7, 2 => .vertical ⟨7, 2⟩ | 7, 3 => .vertical ⟨7, 4⟩
      | 7, 4 => .horizontal ⟨7, 4⟩ | 7, 5 => .vertical ⟨7, 5⟩
      | 7, 6 => .vertical ⟨7, 7⟩ | 7, 7 => .vertical ⟨7, 8⟩
      | 7, 8 => .horizontal ⟨8, 8⟩ | 7, 9 => .vertical ⟨7, 9⟩
      | 7, 10 => .vertical ⟨7, 11⟩ | 7, 11 => .horizontal ⟨7, 11⟩
      | 7, 12 => .vertical ⟨7, 12⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .horizontal ⟨8, 1⟩
      | 8, 2 => .vertical ⟨8, 2⟩ | 8, 3 => .vertical ⟨8, 4⟩
      | 8, 4 => .horizontal ⟨8, 4⟩ | 8, 5 => .vertical ⟨8, 5⟩
      | 8, 6 => .vertical ⟨8, 7⟩ | 8, 7 => .horizontal ⟨8, 7⟩
      | 8, 8 => .vertical ⟨8, 9⟩ | 8, 9 => .horizontal ⟨9, 9⟩
      | 8, 10 => .vertical ⟨8, 11⟩ | 8, 11 => .horizontal ⟨8, 11⟩
      | 8, 12 => .vertical ⟨8, 12⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .horizontal ⟨9, 1⟩
      | 9, 2 => .vertical ⟨9, 2⟩ | 9, 3 => .vertical ⟨9, 4⟩
      | 9, 4 => .horizontal ⟨9, 4⟩ | 9, 5 => .vertical ⟨9, 5⟩
      | 9, 6 => .vertical ⟨9, 7⟩ | 9, 7 => .horizontal ⟨10, 7⟩
      | 9, 8 => .vertical ⟨9, 9⟩ | 9, 9 => .vertical ⟨9, 10⟩
      | 9, 10 => .horizontal ⟨9, 10⟩ | 9, 11 => .horizontal ⟨9, 11⟩
      | 9, 12 => .vertical ⟨9, 12⟩
      | 10, 0 => .vertical ⟨10, 1⟩ | 10, 1 => .horizontal ⟨10, 1⟩
      | 10, 2 => .vertical ⟨10, 2⟩ | 10, 3 => .vertical ⟨10, 4⟩
      | 10, 4 => .horizontal ⟨10, 4⟩ | 10, 5 => .vertical ⟨10, 5⟩
      | 10, 6 => .vertical ⟨10, 7⟩ | 10, 7 => .vertical ⟨10, 8⟩
      | 10, 8 => .horizontal ⟨10, 8⟩ | 10, 9 => .horizontal ⟨10, 9⟩
      | 10, 10 => .vertical ⟨10, 10⟩ | 10, 11 => .horizontal ⟨11, 11⟩
      | 10, 12 => .vertical ⟨10, 12⟩
      | 11, 0 => .vertical ⟨11, 1⟩ | 11, 1 => .horizontal ⟨11, 1⟩
      | 11, 2 => .vertical ⟨11, 2⟩ | 11, 3 => .vertical ⟨11, 4⟩
      | 11, 4 => .horizontal ⟨11, 4⟩ | 11, 5 => .vertical ⟨11, 5⟩
      | 11, 6 => .vertical ⟨11, 7⟩ | 11, 7 => .horizontal ⟨11, 7⟩
      | 11, 8 => .vertical ⟨11, 8⟩ | 11, 9 => .vertical ⟨11, 10⟩
      | 11, 10 => .horizontal ⟨11, 10⟩ | 11, 11 => .vertical ⟨11, 11⟩
      | 11, 12 => .vertical ⟨11, 12⟩
      | 12, 0 => .vertical ⟨12, 1⟩ | 12, 1 => .horizontal ⟨12, 1⟩
      | 12, 2 => .horizontal ⟨12, 2⟩ | 12, 3 => .horizontal ⟨12, 3⟩
      | 12, 4 => .horizontal ⟨12, 4⟩ | 12, 5 => .horizontal ⟨12, 5⟩
      | 12, 6 => .horizontal ⟨12, 6⟩ | 12, 7 => .horizontal ⟨12, 7⟩
      | 12, 8 => .horizontal ⟨12, 8⟩ | 12, 9 => .horizontal ⟨12, 9⟩
      | 12, 10 => .horizontal ⟨12, 10⟩ | 12, 11 => .horizontal ⟨12, 11⟩
      | 12, 12 => .vertical ⟨12, 12⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU14PrimalEdge_adj (e : FiniteU14PrimalEdge)
    (x y : GridFace 14 14) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU14)
    (h₂ : e.primalEndpoints.2 ∈ finiteU14)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU14).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU14_parent_ne (f : GridFace 14 14) (hf : f ≠ .out) :
    f ≠ finiteU14Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> simp [finiteU14Parent]

set_option maxHeartbeats 8000000 in
private theorem finiteU14_parent_edge_data (f : GridFace 14 14) (hf : f ≠ .out) :
    let e := finiteU14ParentEdge f
    e.primalEndpoints.1 ∈ finiteU14 ∧
      e.primalEndpoints.2 ∈ finiteU14 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU14Parent f) := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;>
        norm_num [finiteU14ParentEdge, FiniteU14PrimalEdge.primalEndpoints,
          FiniteU14PrimalEdge.dualEndpoints, finiteU14, finiteU14Selected,
          finiteU14Parent, horizontalPrimalEndpoints, verticalPrimalEndpoints,
          horizontalDualEndpoints, verticalDualEndpoints, HasDualEndpoints,
          Fin.mk.injEq] <;> simp

/-- The explicit ranked parent certificate on all one hundred seventy faces. -/
def finiteU14RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU14) where
  root := .out
  parent := finiteU14Parent
  rank := finiteU14Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU14_parent_edge_data f hf
    exact finiteU14PrimalEdge_adj (finiteU14ParentEdge f) f (finiteU14Parent f)
      (finiteU14_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU14Parent, finiteU14Rank]

theorem finiteU14_compl_card :
    ((Finset.univ : Finset (GridVertex 14 14)) \ finiteU14).card = 77 := by
  have hU : finiteU14.card = 119 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 196 - 119 = 77
  norm_num

/-- Seventy-seven vertices can be preserved in the fourteen-by-fourteen grid. -/
theorem seventySeven_le_maxPreserved_fourteen_fourteen :
    77 ≤ maxPreserved 14 14 := by
  rw [← finiteU14_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU14 finiteU14RankedDualCertificate

end GridGraphs
