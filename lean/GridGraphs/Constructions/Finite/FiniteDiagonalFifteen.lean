import GridGraphs.Constructions.ConstructionCertificate

/-!
# The finite diagonal construction for fifteen rows

This file records the row-mask construction
`[0, 32767, 16374, 8246, 16374, 14038, 14046, 14042, 14046, 14070,
14262, 15798, 11702, 16382, 12290]`. Connectivity of its U-U dual is
certified by explicit parent, rank, and crossed primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- The mask in row `r` of the fifteen-by-fifteen construction. -/
def finiteU15Mask : Nat → Nat
  | 0 => 0 | 1 => 32767 | 2 => 16374 | 3 => 8246 | 4 => 16374
  | 5 => 14038 | 6 => 14046 | 7 => 14042 | 8 => 14046 | 9 => 14070
  | 10 => 14262 | 11 => 15798 | 12 => 11702 | 13 => 16382
  | 14 => 12290 | _ => 0

private def finiteU15Selected (v : GridVertex 15 15) : Bool :=
  match v.1.val with
  | 0 => false
  | 1 => true
  | 2 | 4 => v.2.val == 1 || v.2.val == 2 ||
      (4 ≤ v.2.val && v.2.val ≤ 13)
  | 3 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 13
  | 5 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 6 || v.2.val == 7 || v.2.val == 9 ||
      v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 6 | 8 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 7 => v.2.val == 1 || v.2.val == 3 || v.2.val == 4 ||
      v.2.val == 6 || v.2.val == 7 || v.2.val == 9 ||
      v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 9 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 10 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 8 ||
      v.2.val == 9 || v.2.val == 10 || v.2.val == 12 || v.2.val == 13
  | 11 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 8 ||
      v.2.val == 10 || v.2.val == 11 || v.2.val == 12 || v.2.val == 13
  | 12 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 7 || v.2.val == 8 ||
      v.2.val == 10 || v.2.val == 11 || v.2.val == 13
  | 13 => 1 ≤ v.2.val && v.2.val ≤ 13
  | 14 => v.2.val == 1 || v.2.val == 12 || v.2.val == 13
  | _ => false

/-- The selected vertices with the fifteen specified row masks. -/
def finiteU15 : Finset (GridVertex 15 15) :=
  Finset.univ.filter fun v => finiteU15Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU15Parent : GridFace 15 15 → GridFace 15 15
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 1 0 | 0, 1 => .cell 1 1 | 0, 2 => .cell 1 2
      | 0, 3 => .cell 1 3 | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7 | 0, 8 => .cell 1 8
      | 0, 9 => .cell 1 9 | 0, 10 => .cell 1 10 | 0, 11 => .cell 1 11
      | 0, 12 => .cell 1 12 | 0, 13 => .cell 1 13
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 2 1 | 1, 2 => .cell 1 1
      | 1, 3 => .cell 1 4 | 1, 4 => .cell 2 4 | 1, 5 => .cell 1 4
      | 1, 6 => .cell 1 5 | 1, 7 => .cell 1 6 | 1, 8 => .cell 1 7
      | 1, 9 => .cell 1 8 | 1, 10 => .cell 1 9 | 1, 11 => .cell 1 10
      | 1, 12 => .cell 1 11 | 1, 13 => .cell 1 12
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 3 1 | 2, 2 => .cell 2 1
      | 2, 3 => .cell 2 4 | 2, 4 => .cell 3 4 | 2, 5 => .cell 2 4
      | 2, 6 => .cell 1 6 | 2, 7 => .cell 1 7 | 2, 8 => .cell 1 8
      | 2, 9 => .cell 1 9 | 2, 10 => .cell 1 10 | 2, 11 => .cell 1 11
      | 2, 12 => .cell 1 12 | 2, 13 => .cell 2 12
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 4 1 | 3, 2 => .cell 3 1
      | 3, 3 => .cell 3 4 | 3, 4 => .cell 3 5 | 3, 5 => .cell 4 5
      | 3, 6 => .cell 4 6 | 3, 7 => .cell 4 7 | 3, 8 => .cell 4 8
      | 3, 9 => .cell 4 9 | 3, 10 => .cell 4 10 | 3, 11 => .cell 4 11
      | 3, 12 => .cell 4 12 | 3, 13 => .cell 3 12
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 5 1 | 4, 2 => .cell 4 1
      | 4, 3 => .cell 4 4 | 4, 4 => .cell 3 4 | 4, 5 => .cell 4 6
      | 4, 6 => .cell 5 6 | 4, 7 => .cell 4 6 | 4, 8 => .cell 4 9
      | 4, 9 => .cell 5 9 | 4, 10 => .cell 4 9 | 4, 11 => .cell 4 12
      | 4, 12 => .cell 5 12 | 4, 13 => .cell 4 12
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 5 2 | 5, 2 => .cell 6 2
      | 5, 3 => .cell 6 3 | 5, 4 => .cell 5 3 | 5, 5 => .cell 5 6
      | 5, 6 => .cell 6 6 | 5, 7 => .cell 5 6 | 5, 8 => .cell 5 9
      | 5, 9 => .cell 6 9 | 5, 10 => .cell 5 9 | 5, 11 => .cell 5 12
      | 5, 12 => .cell 6 12 | 5, 13 => .cell 5 12
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 5 1 | 6, 2 => .cell 6 3
      | 6, 3 => .cell 7 3 | 6, 4 => .cell 6 3 | 6, 5 => .cell 6 6
      | 6, 6 => .cell 7 6 | 6, 7 => .cell 6 6 | 6, 8 => .cell 6 9
      | 6, 9 => .cell 7 9 | 6, 10 => .cell 6 9 | 6, 11 => .cell 6 12
      | 6, 12 => .cell 7 12 | 6, 13 => .cell 6 12
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 8 1 | 7, 2 => .cell 7 3
      | 7, 3 => .cell 8 3 | 7, 4 => .cell 7 3 | 7, 5 => .cell 7 6
      | 7, 6 => .cell 8 6 | 7, 7 => .cell 7 6 | 7, 8 => .cell 7 9
      | 7, 9 => .cell 8 9 | 7, 10 => .cell 7 9 | 7, 11 => .cell 7 12
      | 7, 12 => .cell 8 12 | 7, 13 => .cell 7 12
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 8 2 | 8, 2 => .cell 7 2
      | 8, 3 => .cell 8 4 | 8, 4 => .cell 9 4 | 8, 5 => .cell 8 6
      | 8, 6 => .cell 9 6 | 8, 7 => .cell 8 6 | 8, 8 => .cell 8 9
      | 8, 9 => .cell 9 9 | 8, 10 => .cell 8 9 | 8, 11 => .cell 8 12
      | 8, 12 => .cell 9 12 | 8, 13 => .cell 8 12
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 8 1 | 9, 2 => .cell 9 1
      | 9, 3 => .cell 9 4 | 9, 4 => .cell 9 5 | 9, 5 => .cell 8 5
      | 9, 6 => .cell 9 7 | 9, 7 => .cell 10 7 | 9, 8 => .cell 9 9
      | 9, 9 => .cell 10 9 | 9, 10 => .cell 9 9 | 9, 11 => .cell 9 12
      | 9, 12 => .cell 10 12 | 9, 13 => .cell 9 12
      | 10, 0 => .cell 10 1 | 10, 1 => .cell 9 1 | 10, 2 => .cell 10 1
      | 10, 3 => .cell 10 4 | 10, 4 => .cell 9 4 | 10, 5 => .cell 10 4
      | 10, 6 => .cell 10 7 | 10, 7 => .cell 10 8 | 10, 8 => .cell 9 8
      | 10, 9 => .cell 10 10 | 10, 10 => .cell 11 10 | 10, 11 => .cell 11 11
      | 10, 12 => .cell 10 11 | 10, 13 => .cell 10 12
      | 11, 0 => .cell 11 1 | 11, 1 => .cell 10 1 | 11, 2 => .cell 11 1
      | 11, 3 => .cell 11 4 | 11, 4 => .cell 10 4 | 11, 5 => .cell 11 4
      | 11, 6 => .cell 11 7 | 11, 7 => .cell 10 7 | 11, 8 => .cell 11 7
      | 11, 9 => .cell 11 10 | 11, 10 => .cell 12 10 | 11, 11 => .cell 11 10
      | 11, 12 => .cell 10 12 | 11, 13 => .cell 11 12
      | 12, 0 => .cell 12 1 | 12, 1 => .cell 11 1 | 12, 2 => .cell 12 1
      | 12, 3 => .cell 12 4 | 12, 4 => .cell 11 4 | 12, 5 => .cell 12 4
      | 12, 6 => .cell 12 7 | 12, 7 => .cell 11 7 | 12, 8 => .cell 12 7
      | 12, 9 => .cell 12 10 | 12, 10 => .cell 12 11 | 12, 11 => .cell 13 11
      | 12, 12 => .cell 13 12 | 12, 13 => .cell 12 12
      | 13, 0 => .cell 13 1 | 13, 1 => .cell 12 1 | 13, 2 => .cell 12 2
      | 13, 3 => .cell 12 3 | 13, 4 => .cell 12 4 | 13, 5 => .cell 12 5
      | 13, 6 => .cell 12 6 | 13, 7 => .cell 12 7 | 13, 8 => .cell 12 8
      | 13, 9 => .cell 12 9 | 13, 10 => .cell 12 10 | 13, 11 => .cell 13 12
      | 13, 12 => .out | 13, 13 => .cell 13 12
      | _, _ => .out

/-- Depths in `finiteU15Parent`, with the outside face at rank zero. -/
def finiteU15Rank : GridFace 15 15 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 30 | 0, 1 => 29 | 0, 2 => 30 | 0, 3 => 25 | 0, 4 => 24
      | 0, 5 => 25 | 0, 6 => 26 | 0, 7 => 27 | 0, 8 => 28 | 0, 9 => 29
      | 0, 10 => 30 | 0, 11 => 31 | 0, 12 => 32 | 0, 13 => 33
      | 1, 0 => 29 | 1, 1 => 28 | 1, 2 => 29 | 1, 3 => 24 | 1, 4 => 23
      | 1, 5 => 24 | 1, 6 => 25 | 1, 7 => 26 | 1, 8 => 27 | 1, 9 => 28
      | 1, 10 => 29 | 1, 11 => 30 | 1, 12 => 31 | 1, 13 => 32
      | 2, 0 => 28 | 2, 1 => 27 | 2, 2 => 28 | 2, 3 => 23 | 2, 4 => 22
      | 2, 5 => 23 | 2, 6 => 26 | 2, 7 => 27 | 2, 8 => 28 | 2, 9 => 29
      | 2, 10 => 30 | 2, 11 => 31 | 2, 12 => 32 | 2, 13 => 33
      | 3, 0 => 27 | 3, 1 => 26 | 3, 2 => 27 | 3, 3 => 22 | 3, 4 => 21
      | 3, 5 => 20 | 3, 6 => 19 | 3, 7 => 20 | 3, 8 => 15 | 3, 9 => 14
      | 3, 10 => 15 | 3, 11 => 16 | 3, 12 => 15 | 3, 13 => 16
      | 4, 0 => 26 | 4, 1 => 25 | 4, 2 => 26 | 4, 3 => 23 | 4, 4 => 22
      | 4, 5 => 19 | 4, 6 => 18 | 4, 7 => 19 | 4, 8 => 14 | 4, 9 => 13
      | 4, 10 => 14 | 4, 11 => 15 | 4, 12 => 14 | 4, 13 => 15
      | 5, 0 => 25 | 5, 1 => 24 | 5, 2 => 23 | 5, 3 => 22 | 5, 4 => 23
      | 5, 5 => 18 | 5, 6 => 17 | 5, 7 => 18 | 5, 8 => 13 | 5, 9 => 12
      | 5, 10 => 13 | 5, 11 => 14 | 5, 12 => 13 | 5, 13 => 14
      | 6, 0 => 26 | 6, 1 => 25 | 6, 2 => 22 | 6, 3 => 21 | 6, 4 => 22
      | 6, 5 => 17 | 6, 6 => 16 | 6, 7 => 17 | 6, 8 => 12 | 6, 9 => 11
      | 6, 10 => 12 | 6, 11 => 13 | 6, 12 => 12 | 6, 13 => 13
      | 7, 0 => 25 | 7, 1 => 24 | 7, 2 => 21 | 7, 3 => 20 | 7, 4 => 21
      | 7, 5 => 16 | 7, 6 => 15 | 7, 7 => 16 | 7, 8 => 11 | 7, 9 => 10
      | 7, 10 => 11 | 7, 11 => 12 | 7, 12 => 11 | 7, 13 => 12
      | 8, 0 => 24 | 8, 1 => 23 | 8, 2 => 22 | 8, 3 => 19 | 8, 4 => 18
      | 8, 5 => 15 | 8, 6 => 14 | 8, 7 => 15 | 8, 8 => 10 | 8, 9 => 9
      | 8, 10 => 10 | 8, 11 => 11 | 8, 12 => 10 | 8, 13 => 11
      | 9, 0 => 25 | 9, 1 => 24 | 9, 2 => 25 | 9, 3 => 18 | 9, 4 => 17
      | 9, 5 => 16 | 9, 6 => 13 | 9, 7 => 12 | 9, 8 => 9 | 9, 9 => 8
      | 9, 10 => 9 | 9, 11 => 10 | 9, 12 => 9 | 9, 13 => 10
      | 10, 0 => 26 | 10, 1 => 25 | 10, 2 => 26 | 10, 3 => 19 | 10, 4 => 18
      | 10, 5 => 19 | 10, 6 => 12 | 10, 7 => 11 | 10, 8 => 10 | 10, 9 => 7
      | 10, 10 => 6 | 10, 11 => 7 | 10, 12 => 8 | 10, 13 => 9
      | 11, 0 => 27 | 11, 1 => 26 | 11, 2 => 27 | 11, 3 => 20 | 11, 4 => 19
      | 11, 5 => 20 | 11, 6 => 13 | 11, 7 => 12 | 11, 8 => 13 | 11, 9 => 6
      | 11, 10 => 5 | 11, 11 => 6 | 11, 12 => 9 | 11, 13 => 10
      | 12, 0 => 28 | 12, 1 => 27 | 12, 2 => 28 | 12, 3 => 21 | 12, 4 => 20
      | 12, 5 => 21 | 12, 6 => 14 | 12, 7 => 13 | 12, 8 => 14 | 12, 9 => 5
      | 12, 10 => 4 | 12, 11 => 3 | 12, 12 => 2 | 12, 13 => 3
      | 13, 0 => 29 | 13, 1 => 28 | 13, 2 => 29 | 13, 3 => 22 | 13, 4 => 21
      | 13, 5 => 22 | 13, 6 => 15 | 13, 7 => 14 | 13, 8 => 15 | 13, 9 => 6
      | 13, 10 => 5 | 13, 11 => 2 | 13, 12 => 1 | 13, 13 => 2
      | _, _ => 0

private inductive FiniteU15PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 15 15)
  | vertical (edge : VerticalGridEdge 15 15)

private def FiniteU15PrimalEdge.primalEndpoints :
    FiniteU15PrimalEdge → GridVertex 15 15 × GridVertex 15 15
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU15PrimalEdge.dualEndpoints :
    FiniteU15PrimalEdge → GridFace 15 15 × GridFace 15 15
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU15ParentEdge : GridFace 15 15 → FiniteU15PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .horizontal ⟨1, 0⟩ | 0, 1 => .horizontal ⟨1, 1⟩
      | 0, 2 => .horizontal ⟨1, 2⟩ | 0, 3 => .horizontal ⟨1, 3⟩
      | 0, 4 => .horizontal ⟨1, 4⟩ | 0, 5 => .horizontal ⟨1, 5⟩
      | 0, 6 => .horizontal ⟨1, 6⟩ | 0, 7 => .horizontal ⟨1, 7⟩
      | 0, 8 => .horizontal ⟨1, 8⟩ | 0, 9 => .horizontal ⟨1, 9⟩
      | 0, 10 => .horizontal ⟨1, 10⟩ | 0, 11 => .horizontal ⟨1, 11⟩
      | 0, 12 => .horizontal ⟨1, 12⟩ | 0, 13 => .horizontal ⟨1, 13⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .horizontal ⟨2, 1⟩
      | 1, 2 => .vertical ⟨1, 2⟩ | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .horizontal ⟨2, 4⟩ | 1, 5 => .vertical ⟨1, 5⟩
      | 1, 6 => .vertical ⟨1, 6⟩ | 1, 7 => .vertical ⟨1, 7⟩
      | 1, 8 => .vertical ⟨1, 8⟩ | 1, 9 => .vertical ⟨1, 9⟩
      | 1, 10 => .vertical ⟨1, 10⟩ | 1, 11 => .vertical ⟨1, 11⟩
      | 1, 12 => .vertical ⟨1, 12⟩ | 1, 13 => .vertical ⟨1, 13⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .horizontal ⟨3, 1⟩
      | 2, 2 => .vertical ⟨2, 2⟩ | 2, 3 => .vertical ⟨2, 4⟩
      | 2, 4 => .horizontal ⟨3, 4⟩ | 2, 5 => .vertical ⟨2, 5⟩
      | 2, 6 => .horizontal ⟨2, 6⟩ | 2, 7 => .horizontal ⟨2, 7⟩
      | 2, 8 => .horizontal ⟨2, 8⟩ | 2, 9 => .horizontal ⟨2, 9⟩
      | 2, 10 => .horizontal ⟨2, 10⟩ | 2, 11 => .horizontal ⟨2, 11⟩
      | 2, 12 => .horizontal ⟨2, 12⟩ | 2, 13 => .vertical ⟨2, 13⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨4, 1⟩
      | 3, 2 => .vertical ⟨3, 2⟩ | 3, 3 => .vertical ⟨3, 4⟩
      | 3, 4 => .vertical ⟨3, 5⟩ | 3, 5 => .horizontal ⟨4, 5⟩
      | 3, 6 => .horizontal ⟨4, 6⟩ | 3, 7 => .horizontal ⟨4, 7⟩
      | 3, 8 => .horizontal ⟨4, 8⟩ | 3, 9 => .horizontal ⟨4, 9⟩
      | 3, 10 => .horizontal ⟨4, 10⟩ | 3, 11 => .horizontal ⟨4, 11⟩
      | 3, 12 => .horizontal ⟨4, 12⟩ | 3, 13 => .vertical ⟨3, 13⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .horizontal ⟨5, 1⟩
      | 4, 2 => .vertical ⟨4, 2⟩ | 4, 3 => .vertical ⟨4, 4⟩
      | 4, 4 => .horizontal ⟨4, 4⟩ | 4, 5 => .vertical ⟨4, 6⟩
      | 4, 6 => .horizontal ⟨5, 6⟩ | 4, 7 => .vertical ⟨4, 7⟩
      | 4, 8 => .vertical ⟨4, 9⟩ | 4, 9 => .horizontal ⟨5, 9⟩
      | 4, 10 => .vertical ⟨4, 10⟩ | 4, 11 => .vertical ⟨4, 12⟩
      | 4, 12 => .horizontal ⟨5, 12⟩ | 4, 13 => .vertical ⟨4, 13⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .vertical ⟨5, 2⟩
      | 5, 2 => .horizontal ⟨6, 2⟩ | 5, 3 => .horizontal ⟨6, 3⟩
      | 5, 4 => .vertical ⟨5, 4⟩ | 5, 5 => .vertical ⟨5, 6⟩
      | 5, 6 => .horizontal ⟨6, 6⟩ | 5, 7 => .vertical ⟨5, 7⟩
      | 5, 8 => .vertical ⟨5, 9⟩ | 5, 9 => .horizontal ⟨6, 9⟩
      | 5, 10 => .vertical ⟨5, 10⟩ | 5, 11 => .vertical ⟨5, 12⟩
      | 5, 12 => .horizontal ⟨6, 12⟩ | 5, 13 => .vertical ⟨5, 13⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨6, 1⟩
      | 6, 2 => .vertical ⟨6, 3⟩ | 6, 3 => .horizontal ⟨7, 3⟩
      | 6, 4 => .vertical ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 6⟩
      | 6, 6 => .horizontal ⟨7, 6⟩ | 6, 7 => .vertical ⟨6, 7⟩
      | 6, 8 => .vertical ⟨6, 9⟩ | 6, 9 => .horizontal ⟨7, 9⟩
      | 6, 10 => .vertical ⟨6, 10⟩ | 6, 11 => .vertical ⟨6, 12⟩
      | 6, 12 => .horizontal ⟨7, 12⟩ | 6, 13 => .vertical ⟨6, 13⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨8, 1⟩
      | 7, 2 => .vertical ⟨7, 3⟩ | 7, 3 => .horizontal ⟨8, 3⟩
      | 7, 4 => .vertical ⟨7, 4⟩ | 7, 5 => .vertical ⟨7, 6⟩
      | 7, 6 => .horizontal ⟨8, 6⟩ | 7, 7 => .vertical ⟨7, 7⟩
      | 7, 8 => .vertical ⟨7, 9⟩ | 7, 9 => .horizontal ⟨8, 9⟩
      | 7, 10 => .vertical ⟨7, 10⟩ | 7, 11 => .vertical ⟨7, 12⟩
      | 7, 12 => .horizontal ⟨8, 12⟩ | 7, 13 => .vertical ⟨7, 13⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .vertical ⟨8, 2⟩
      | 8, 2 => .horizontal ⟨8, 2⟩ | 8, 3 => .vertical ⟨8, 4⟩
      | 8, 4 => .horizontal ⟨9, 4⟩ | 8, 5 => .vertical ⟨8, 6⟩
      | 8, 6 => .horizontal ⟨9, 6⟩ | 8, 7 => .vertical ⟨8, 7⟩
      | 8, 8 => .vertical ⟨8, 9⟩ | 8, 9 => .horizontal ⟨9, 9⟩
      | 8, 10 => .vertical ⟨8, 10⟩ | 8, 11 => .vertical ⟨8, 12⟩
      | 8, 12 => .horizontal ⟨9, 12⟩ | 8, 13 => .vertical ⟨8, 13⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .horizontal ⟨9, 1⟩
      | 9, 2 => .vertical ⟨9, 2⟩ | 9, 3 => .vertical ⟨9, 4⟩
      | 9, 4 => .vertical ⟨9, 5⟩ | 9, 5 => .horizontal ⟨9, 5⟩
      | 9, 6 => .vertical ⟨9, 7⟩ | 9, 7 => .horizontal ⟨10, 7⟩
      | 9, 8 => .vertical ⟨9, 9⟩ | 9, 9 => .horizontal ⟨10, 9⟩
      | 9, 10 => .vertical ⟨9, 10⟩ | 9, 11 => .vertical ⟨9, 12⟩
      | 9, 12 => .horizontal ⟨10, 12⟩ | 9, 13 => .vertical ⟨9, 13⟩
      | 10, 0 => .vertical ⟨10, 1⟩ | 10, 1 => .horizontal ⟨10, 1⟩
      | 10, 2 => .vertical ⟨10, 2⟩ | 10, 3 => .vertical ⟨10, 4⟩
      | 10, 4 => .horizontal ⟨10, 4⟩ | 10, 5 => .vertical ⟨10, 5⟩
      | 10, 6 => .vertical ⟨10, 7⟩ | 10, 7 => .vertical ⟨10, 8⟩
      | 10, 8 => .horizontal ⟨10, 8⟩ | 10, 9 => .vertical ⟨10, 10⟩
      | 10, 10 => .horizontal ⟨11, 10⟩ | 10, 11 => .horizontal ⟨11, 11⟩
      | 10, 12 => .vertical ⟨10, 12⟩ | 10, 13 => .vertical ⟨10, 13⟩
      | 11, 0 => .vertical ⟨11, 1⟩ | 11, 1 => .horizontal ⟨11, 1⟩
      | 11, 2 => .vertical ⟨11, 2⟩ | 11, 3 => .vertical ⟨11, 4⟩
      | 11, 4 => .horizontal ⟨11, 4⟩ | 11, 5 => .vertical ⟨11, 5⟩
      | 11, 6 => .vertical ⟨11, 7⟩ | 11, 7 => .horizontal ⟨11, 7⟩
      | 11, 8 => .vertical ⟨11, 8⟩ | 11, 9 => .vertical ⟨11, 10⟩
      | 11, 10 => .horizontal ⟨12, 10⟩ | 11, 11 => .vertical ⟨11, 11⟩
      | 11, 12 => .horizontal ⟨11, 12⟩ | 11, 13 => .vertical ⟨11, 13⟩
      | 12, 0 => .vertical ⟨12, 1⟩ | 12, 1 => .horizontal ⟨12, 1⟩
      | 12, 2 => .vertical ⟨12, 2⟩ | 12, 3 => .vertical ⟨12, 4⟩
      | 12, 4 => .horizontal ⟨12, 4⟩ | 12, 5 => .vertical ⟨12, 5⟩
      | 12, 6 => .vertical ⟨12, 7⟩ | 12, 7 => .horizontal ⟨12, 7⟩
      | 12, 8 => .vertical ⟨12, 8⟩ | 12, 9 => .vertical ⟨12, 10⟩
      | 12, 10 => .vertical ⟨12, 11⟩ | 12, 11 => .horizontal ⟨13, 11⟩
      | 12, 12 => .horizontal ⟨13, 12⟩ | 12, 13 => .vertical ⟨12, 13⟩
      | 13, 0 => .vertical ⟨13, 1⟩ | 13, 1 => .horizontal ⟨13, 1⟩
      | 13, 2 => .horizontal ⟨13, 2⟩ | 13, 3 => .horizontal ⟨13, 3⟩
      | 13, 4 => .horizontal ⟨13, 4⟩ | 13, 5 => .horizontal ⟨13, 5⟩
      | 13, 6 => .horizontal ⟨13, 6⟩ | 13, 7 => .horizontal ⟨13, 7⟩
      | 13, 8 => .horizontal ⟨13, 8⟩ | 13, 9 => .horizontal ⟨13, 9⟩
      | 13, 10 => .horizontal ⟨13, 10⟩ | 13, 11 => .vertical ⟨13, 12⟩
      | 13, 12 => .horizontal ⟨14, 12⟩ | 13, 13 => .vertical ⟨13, 13⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU15PrimalEdge_adj (e : FiniteU15PrimalEdge)
    (x y : GridFace 15 15) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU15)
    (h₂ : e.primalEndpoints.2 ∈ finiteU15)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU15).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU15_parent_ne (f : GridFace 15 15) (hf : f ≠ .out) :
    f ≠ finiteU15Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

private theorem finiteU15_parent_edge_data (f : GridFace 15 15) (hf : f ≠ .out) :
    let e := finiteU15ParentEdge f
    e.primalEndpoints.1 ∈ finiteU15 ∧
      e.primalEndpoints.2 ∈ finiteU15 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU15Parent f) := by
  simp only [finiteU15, Finset.mem_filter, Finset.mem_univ, true_and, HasDualEndpoints]
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

/-- The explicit ranked parent certificate on all one hundred ninety-seven faces. -/
def finiteU15RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU15) where
  root := .out
  parent := finiteU15Parent
  rank := finiteU15Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU15_parent_edge_data f hf
    exact finiteU15PrimalEdge_adj (finiteU15ParentEdge f) f (finiteU15Parent f)
      (finiteU15_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;> decide

theorem finiteU15_compl_card :
    ((Finset.univ : Finset (GridVertex 15 15)) \ finiteU15).card = 88 := by
  have hU : finiteU15.card = 137 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 225 - 137 = 88
  norm_num

/-- Eighty-eight vertices can be preserved in the fifteen-by-fifteen grid. -/
theorem eightyEight_le_maxPreserved_fifteen_fifteen :
    88 ≤ maxPreserved 15 15 := by
  rw [← finiteU15_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU15 finiteU15RankedDualCertificate

end GridGraphs
