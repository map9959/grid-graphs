import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for eighteen rows

This file records the row-mask construction
`[0, 262143, 130998, 65974, 130998, 112374, 112350, 112346, 112350,
112342, 112374, 112310, 112566, 114102, 126390, 93622, 131070, 98306]`.
Connectivity of its U-U dual is certified by explicit parent, rank, and crossed
primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- The mask in row `r` of the eighteen-by-eighteen construction. -/
def finiteU18Mask : Nat → Nat
  | 0 => 0 | 1 => 262143 | 2 => 130998 | 3 => 65974
  | 4 => 130998 | 5 => 112374 | 6 => 112350 | 7 => 112346
  | 8 => 112350 | 9 => 112342 | 10 => 112374 | 11 => 112310
  | 12 => 112566 | 13 => 114102 | 14 => 126390 | 15 => 93622
  | 16 => 131070 | 17 => 98306 | _ => 0

private def finiteU18Selected (v : GridVertex 18 18) : Bool :=
  match v.1.val with
  | 0 => false
  | 1 => true
  | 2 | 4 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 16)
  | 3 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) ||
      (7 ≤ v.2.val && v.2.val ≤ 8) || v.2.val == 16
  | 5 | 10 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 7) ||
      (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 6 | 8 => (1 ≤ v.2.val && v.2.val ≤ 4) ||
      (6 ≤ v.2.val && v.2.val ≤ 7) ||
      (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 7 => v.2.val == 1 || (3 ≤ v.2.val && v.2.val ≤ 4) ||
      (6 ≤ v.2.val && v.2.val ≤ 7) ||
      (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 9 => (1 ≤ v.2.val && v.2.val ≤ 2) || v.2.val == 4 ||
      (6 ≤ v.2.val && v.2.val ≤ 7) ||
      (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 11 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || v.2.val == 7 ||
      (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 12 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) ||
      (7 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 13 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) ||
      (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 14 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) ||
      (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 11) || (13 ≤ v.2.val && v.2.val ≤ 16)
  | 15 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) ||
      (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 11) ||
      (13 ≤ v.2.val && v.2.val ≤ 14) || v.2.val == 16
  | 16 => 1 ≤ v.2.val && v.2.val ≤ 16
  | 17 => v.2.val == 1 || (15 ≤ v.2.val && v.2.val ≤ 16)
  | _ => false

/-- The selected vertices with the eighteen specified row masks. -/
def finiteU18 : Finset (GridVertex 18 18) :=
  Finset.univ.filter fun v => finiteU18Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU18Parent : GridFace 18 18 → GridFace 18 18
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 1 0 | 0, 1 => .cell 1 1 | 0, 2 => .cell 1 2
      | 0, 3 => .cell 1 3 | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7 | 0, 8 => .cell 1 8
      | 0, 9 => .cell 1 9 | 0, 10 => .cell 1 10 | 0, 11 => .cell 1 11
      | 0, 12 => .cell 1 12 | 0, 13 => .cell 1 13 | 0, 14 => .cell 1 14
      | 0, 15 => .cell 1 15 | 0, 16 => .cell 1 16
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 2 1 | 1, 2 => .cell 1 1
      | 1, 3 => .cell 1 4 | 1, 4 => .cell 2 4 | 1, 5 => .cell 1 4
      | 1, 6 => .cell 1 7 | 1, 7 => .cell 2 7 | 1, 8 => .cell 2 8
      | 1, 9 => .cell 1 8 | 1, 10 => .cell 1 9 | 1, 11 => .cell 1 10
      | 1, 12 => .cell 1 11 | 1, 13 => .cell 1 12 | 1, 14 => .cell 1 13
      | 1, 15 => .cell 1 14 | 1, 16 => .cell 1 15
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 3 1 | 2, 2 => .cell 2 1
      | 2, 3 => .cell 2 4 | 2, 4 => .cell 3 4 | 2, 5 => .cell 2 4
      | 2, 6 => .cell 2 7 | 2, 7 => .cell 3 7 | 2, 8 => .cell 2 7
      | 2, 9 => .cell 1 9 | 2, 10 => .cell 1 10 | 2, 11 => .cell 1 11
      | 2, 12 => .cell 1 12 | 2, 13 => .cell 1 13 | 2, 14 => .cell 1 14
      | 2, 15 => .cell 1 15 | 2, 16 => .cell 2 15
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 4 1 | 3, 2 => .cell 3 1
      | 3, 3 => .cell 3 4 | 3, 4 => .cell 4 4 | 3, 5 => .cell 3 4
      | 3, 6 => .cell 3 7 | 3, 7 => .cell 3 8 | 3, 8 => .cell 4 8
      | 3, 9 => .cell 4 9 | 3, 10 => .cell 4 10 | 3, 11 => .cell 4 11
      | 3, 12 => .cell 4 12 | 3, 13 => .cell 4 13 | 3, 14 => .cell 4 14
      | 3, 15 => .cell 4 15 | 3, 16 => .cell 3 15
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 5 1 | 4, 2 => .cell 4 1
      | 4, 3 => .cell 4 4 | 4, 4 => .cell 4 5 | 4, 5 => .cell 5 5
      | 4, 6 => .cell 4 7 | 4, 7 => .cell 3 7 | 4, 8 => .cell 4 9
      | 4, 9 => .cell 5 9 | 4, 10 => .cell 4 9 | 4, 11 => .cell 4 12
      | 4, 12 => .cell 5 12 | 4, 13 => .cell 4 12 | 4, 14 => .cell 4 15
      | 4, 15 => .cell 5 15 | 4, 16 => .cell 4 15
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 5 2 | 5, 2 => .cell 6 2
      | 5, 3 => .cell 5 4 | 5, 4 => .cell 4 4 | 5, 5 => .cell 5 6
      | 5, 6 => .cell 4 6 | 5, 7 => .cell 5 6 | 5, 8 => .cell 5 9
      | 5, 9 => .cell 6 9 | 5, 10 => .cell 5 9 | 5, 11 => .cell 5 12
      | 5, 12 => .cell 6 12 | 5, 13 => .cell 5 12 | 5, 14 => .cell 5 15
      | 5, 15 => .cell 6 15 | 5, 16 => .cell 5 15
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 5 1 | 6, 2 => .cell 6 3
      | 6, 3 => .cell 5 3 | 6, 4 => .cell 6 3 | 6, 5 => .cell 6 6
      | 6, 6 => .cell 5 6 | 6, 7 => .cell 6 6 | 6, 8 => .cell 6 9
      | 6, 9 => .cell 7 9 | 6, 10 => .cell 6 9 | 6, 11 => .cell 6 12
      | 6, 12 => .cell 7 12 | 6, 13 => .cell 6 12 | 6, 14 => .cell 6 15
      | 6, 15 => .cell 7 15 | 6, 16 => .cell 6 15
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 8 1 | 7, 2 => .cell 7 3
      | 7, 3 => .cell 6 3 | 7, 4 => .cell 7 3 | 7, 5 => .cell 7 6
      | 7, 6 => .cell 6 6 | 7, 7 => .cell 7 6 | 7, 8 => .cell 7 9
      | 7, 9 => .cell 8 9 | 7, 10 => .cell 7 9 | 7, 11 => .cell 7 12
      | 7, 12 => .cell 8 12 | 7, 13 => .cell 7 12 | 7, 14 => .cell 7 15
      | 7, 15 => .cell 8 15 | 7, 16 => .cell 7 15
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 8 2 | 8, 2 => .cell 7 2
      | 8, 3 => .cell 7 3 | 8, 4 => .cell 8 3 | 8, 5 => .cell 8 6
      | 8, 6 => .cell 7 6 | 8, 7 => .cell 8 6 | 8, 8 => .cell 8 9
      | 8, 9 => .cell 9 9 | 8, 10 => .cell 8 9 | 8, 11 => .cell 8 12
      | 8, 12 => .cell 9 12 | 8, 13 => .cell 8 12 | 8, 14 => .cell 8 15
      | 8, 15 => .cell 9 15 | 8, 16 => .cell 8 15
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 8 1 | 9, 2 => .cell 9 1
      | 9, 3 => .cell 9 4 | 9, 4 => .cell 10 4 | 9, 5 => .cell 9 6
      | 9, 6 => .cell 8 6 | 9, 7 => .cell 9 6 | 9, 8 => .cell 9 9
      | 9, 9 => .cell 10 9 | 9, 10 => .cell 9 9 | 9, 11 => .cell 9 12
      | 9, 12 => .cell 10 12 | 9, 13 => .cell 9 12 | 9, 14 => .cell 9 15
      | 9, 15 => .cell 10 15 | 9, 16 => .cell 9 15
      | 10, 0 => .cell 10 1 | 10, 1 => .cell 9 1 | 10, 2 => .cell 10 1
      | 10, 3 => .cell 10 4 | 10, 4 => .cell 10 5 | 10, 5 => .cell 9 5
      | 10, 6 => .cell 9 6 | 10, 7 => .cell 10 6 | 10, 8 => .cell 10 9
      | 10, 9 => .cell 11 9 | 10, 10 => .cell 10 9 | 10, 11 => .cell 10 12
      | 10, 12 => .cell 11 12 | 10, 13 => .cell 10 12 | 10, 14 => .cell 10 15
      | 10, 15 => .cell 11 15 | 10, 16 => .cell 10 15
      | 11, 0 => .cell 11 1 | 11, 1 => .cell 10 1 | 11, 2 => .cell 11 1
      | 11, 3 => .cell 11 4 | 11, 4 => .cell 10 4 | 11, 5 => .cell 11 4
      | 11, 6 => .cell 11 7 | 11, 7 => .cell 12 7 | 11, 8 => .cell 11 9
      | 11, 9 => .cell 12 9 | 11, 10 => .cell 11 9 | 11, 11 => .cell 11 12
      | 11, 12 => .cell 12 12 | 11, 13 => .cell 11 12 | 11, 14 => .cell 11 15
      | 11, 15 => .cell 12 15 | 11, 16 => .cell 11 15
      | 12, 0 => .cell 12 1 | 12, 1 => .cell 11 1 | 12, 2 => .cell 12 1
      | 12, 3 => .cell 12 4 | 12, 4 => .cell 11 4 | 12, 5 => .cell 12 4
      | 12, 6 => .cell 12 7 | 12, 7 => .cell 12 8 | 12, 8 => .cell 11 8
      | 12, 9 => .cell 12 10 | 12, 10 => .cell 13 10 | 12, 11 => .cell 12 12
      | 12, 12 => .cell 13 12 | 12, 13 => .cell 12 12 | 12, 14 => .cell 12 15
      | 12, 15 => .cell 13 15 | 12, 16 => .cell 12 15
      | 13, 0 => .cell 13 1 | 13, 1 => .cell 12 1 | 13, 2 => .cell 13 1
      | 13, 3 => .cell 13 4 | 13, 4 => .cell 12 4 | 13, 5 => .cell 13 4
      | 13, 6 => .cell 13 7 | 13, 7 => .cell 12 7 | 13, 8 => .cell 13 7
      | 13, 9 => .cell 13 10 | 13, 10 => .cell 13 11 | 13, 11 => .cell 12 11
      | 13, 12 => .cell 13 13 | 13, 13 => .cell 14 13 | 13, 14 => .cell 14 14
      | 13, 15 => .cell 13 14 | 13, 16 => .cell 13 15
      | 14, 0 => .cell 14 1 | 14, 1 => .cell 13 1 | 14, 2 => .cell 14 1
      | 14, 3 => .cell 14 4 | 14, 4 => .cell 13 4 | 14, 5 => .cell 14 4
      | 14, 6 => .cell 14 7 | 14, 7 => .cell 13 7 | 14, 8 => .cell 14 7
      | 14, 9 => .cell 14 10 | 14, 10 => .cell 13 10 | 14, 11 => .cell 14 10
      | 14, 12 => .cell 14 13 | 14, 13 => .cell 15 13 | 14, 14 => .cell 14 13
      | 14, 15 => .cell 13 15 | 14, 16 => .cell 14 15
      | 15, 0 => .cell 15 1 | 15, 1 => .cell 14 1 | 15, 2 => .cell 15 1
      | 15, 3 => .cell 15 4 | 15, 4 => .cell 14 4 | 15, 5 => .cell 15 4
      | 15, 6 => .cell 15 7 | 15, 7 => .cell 14 7 | 15, 8 => .cell 15 7
      | 15, 9 => .cell 15 10 | 15, 10 => .cell 14 10 | 15, 11 => .cell 15 10
      | 15, 12 => .cell 15 13 | 15, 13 => .cell 15 14 | 15, 14 => .cell 16 14
      | 15, 15 => .cell 16 15 | 15, 16 => .cell 15 15
      | 16, 0 => .cell 16 1 | 16, 1 => .cell 15 1 | 16, 2 => .cell 15 2
      | 16, 3 => .cell 15 3 | 16, 4 => .cell 15 4 | 16, 5 => .cell 15 5
      | 16, 6 => .cell 15 6 | 16, 7 => .cell 15 7 | 16, 8 => .cell 15 8
      | 16, 9 => .cell 15 9 | 16, 10 => .cell 15 10 | 16, 11 => .cell 15 11
      | 16, 12 => .cell 15 12 | 16, 13 => .cell 15 13 | 16, 14 => .cell 16 15
      | 16, 15 => .out | 16, 16 => .cell 16 15
      | _, _ => .out

/-- Depths in `finiteU18Parent`, with the outside face at rank zero. -/
def finiteU18Rank : GridFace 18 18 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 42 | 0, 1 => 41 | 0, 2 => 42 | 0, 3 => 35 | 0, 4 => 34
      | 0, 5 => 35 | 0, 6 => 28 | 0, 7 => 27 | 0, 8 => 28 | 0, 9 => 29
      | 0, 10 => 30 | 0, 11 => 31 | 0, 12 => 32 | 0, 13 => 33
      | 0, 14 => 34 | 0, 15 => 35 | 0, 16 => 36
      | 1, 0 => 41 | 1, 1 => 40 | 1, 2 => 41 | 1, 3 => 34 | 1, 4 => 33
      | 1, 5 => 34 | 1, 6 => 27 | 1, 7 => 26 | 1, 8 => 27 | 1, 9 => 28
      | 1, 10 => 29 | 1, 11 => 30 | 1, 12 => 31 | 1, 13 => 32
      | 1, 14 => 33 | 1, 15 => 34 | 1, 16 => 35
      | 2, 0 => 40 | 2, 1 => 39 | 2, 2 => 40 | 2, 3 => 33 | 2, 4 => 32
      | 2, 5 => 33 | 2, 6 => 26 | 2, 7 => 25 | 2, 8 => 26 | 2, 9 => 29
      | 2, 10 => 30 | 2, 11 => 31 | 2, 12 => 32 | 2, 13 => 33
      | 2, 14 => 34 | 2, 15 => 35 | 2, 16 => 36
      | 3, 0 => 39 | 3, 1 => 38 | 3, 2 => 39 | 3, 3 => 32 | 3, 4 => 31
      | 3, 5 => 32 | 3, 6 => 25 | 3, 7 => 24 | 3, 8 => 23 | 3, 9 => 22
      | 3, 10 => 23 | 3, 11 => 18 | 3, 12 => 17 | 3, 13 => 18
      | 3, 14 => 19 | 3, 15 => 18 | 3, 16 => 19
      | 4, 0 => 38 | 4, 1 => 37 | 4, 2 => 38 | 4, 3 => 31 | 4, 4 => 30
      | 4, 5 => 29 | 4, 6 => 26 | 4, 7 => 25 | 4, 8 => 22 | 4, 9 => 21
      | 4, 10 => 22 | 4, 11 => 17 | 4, 12 => 16 | 4, 13 => 17
      | 4, 14 => 18 | 4, 15 => 17 | 4, 16 => 18
      | 5, 0 => 37 | 5, 1 => 36 | 5, 2 => 35 | 5, 3 => 32 | 5, 4 => 31
      | 5, 5 => 28 | 5, 6 => 27 | 5, 7 => 28 | 5, 8 => 21 | 5, 9 => 20
      | 5, 10 => 21 | 5, 11 => 16 | 5, 12 => 15 | 5, 13 => 16
      | 5, 14 => 17 | 5, 15 => 16 | 5, 16 => 17
      | 6, 0 => 38 | 6, 1 => 37 | 6, 2 => 34 | 6, 3 => 33 | 6, 4 => 34
      | 6, 5 => 29 | 6, 6 => 28 | 6, 7 => 29 | 6, 8 => 20 | 6, 9 => 19
      | 6, 10 => 20 | 6, 11 => 15 | 6, 12 => 14 | 6, 13 => 15
      | 6, 14 => 16 | 6, 15 => 15 | 6, 16 => 16
      | 7, 0 => 39 | 7, 1 => 38 | 7, 2 => 35 | 7, 3 => 34 | 7, 4 => 35
      | 7, 5 => 30 | 7, 6 => 29 | 7, 7 => 30 | 7, 8 => 19 | 7, 9 => 18
      | 7, 10 => 19 | 7, 11 => 14 | 7, 12 => 13 | 7, 13 => 14
      | 7, 14 => 15 | 7, 15 => 14 | 7, 16 => 15
      | 8, 0 => 38 | 8, 1 => 37 | 8, 2 => 36 | 8, 3 => 35 | 8, 4 => 36
      | 8, 5 => 31 | 8, 6 => 30 | 8, 7 => 31 | 8, 8 => 18 | 8, 9 => 17
      | 8, 10 => 18 | 8, 11 => 13 | 8, 12 => 12 | 8, 13 => 13
      | 8, 14 => 14 | 8, 15 => 13 | 8, 16 => 14
      | 9, 0 => 39 | 9, 1 => 38 | 9, 2 => 39 | 9, 3 => 36 | 9, 4 => 35
      | 9, 5 => 32 | 9, 6 => 31 | 9, 7 => 32 | 9, 8 => 17 | 9, 9 => 16
      | 9, 10 => 17 | 9, 11 => 12 | 9, 12 => 11 | 9, 13 => 12
      | 9, 14 => 13 | 9, 15 => 12 | 9, 16 => 13
      | 10, 0 => 40 | 10, 1 => 39 | 10, 2 => 40 | 10, 3 => 35
      | 10, 4 => 34 | 10, 5 => 33 | 10, 6 => 32 | 10, 7 => 33
      | 10, 8 => 16 | 10, 9 => 15 | 10, 10 => 16 | 10, 11 => 11
      | 10, 12 => 10 | 10, 13 => 11 | 10, 14 => 12 | 10, 15 => 11
      | 10, 16 => 12
      | 11, 0 => 41 | 11, 1 => 40 | 11, 2 => 41 | 11, 3 => 36
      | 11, 4 => 35 | 11, 5 => 36 | 11, 6 => 19 | 11, 7 => 18
      | 11, 8 => 15 | 11, 9 => 14 | 11, 10 => 15 | 11, 11 => 10
      | 11, 12 => 9 | 11, 13 => 10 | 11, 14 => 11 | 11, 15 => 10
      | 11, 16 => 11
      | 12, 0 => 42 | 12, 1 => 41 | 12, 2 => 42 | 12, 3 => 37
      | 12, 4 => 36 | 12, 5 => 37 | 12, 6 => 18 | 12, 7 => 17
      | 12, 8 => 16 | 12, 9 => 13 | 12, 10 => 12 | 12, 11 => 9
      | 12, 12 => 8 | 12, 13 => 9 | 12, 14 => 10 | 12, 15 => 9
      | 12, 16 => 10
      | 13, 0 => 43 | 13, 1 => 42 | 13, 2 => 43 | 13, 3 => 38
      | 13, 4 => 37 | 13, 5 => 38 | 13, 6 => 19 | 13, 7 => 18
      | 13, 8 => 19 | 13, 9 => 12 | 13, 10 => 11 | 13, 11 => 10
      | 13, 12 => 7 | 13, 13 => 6 | 13, 14 => 7 | 13, 15 => 8
      | 13, 16 => 9
      | 14, 0 => 44 | 14, 1 => 43 | 14, 2 => 44 | 14, 3 => 39
      | 14, 4 => 38 | 14, 5 => 39 | 14, 6 => 20 | 14, 7 => 19
      | 14, 8 => 20 | 14, 9 => 13 | 14, 10 => 12 | 14, 11 => 13
      | 14, 12 => 6 | 14, 13 => 5 | 14, 14 => 6 | 14, 15 => 9
      | 14, 16 => 10
      | 15, 0 => 45 | 15, 1 => 44 | 15, 2 => 45 | 15, 3 => 40
      | 15, 4 => 39 | 15, 5 => 40 | 15, 6 => 21 | 15, 7 => 20
      | 15, 8 => 21 | 15, 9 => 14 | 15, 10 => 13 | 15, 11 => 14
      | 15, 12 => 5 | 15, 13 => 4 | 15, 14 => 3 | 15, 15 => 2
      | 15, 16 => 3
      | 16, 0 => 46 | 16, 1 => 45 | 16, 2 => 46 | 16, 3 => 41
      | 16, 4 => 40 | 16, 5 => 41 | 16, 6 => 22 | 16, 7 => 21
      | 16, 8 => 22 | 16, 9 => 15 | 16, 10 => 14 | 16, 11 => 15
      | 16, 12 => 6 | 16, 13 => 5 | 16, 14 => 2 | 16, 15 => 1
      | 16, 16 => 2
      | _, _ => 0

private inductive FiniteU18PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 18 18)
  | vertical (edge : VerticalGridEdge 18 18)

private def FiniteU18PrimalEdge.primalEndpoints :
    FiniteU18PrimalEdge → GridVertex 18 18 × GridVertex 18 18
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU18PrimalEdge.dualEndpoints :
    FiniteU18PrimalEdge → GridFace 18 18 × GridFace 18 18
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU18ParentEdge : GridFace 18 18 → FiniteU18PrimalEdge
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
      | 0, 14 => .horizontal ⟨1, 14⟩ | 0, 15 => .horizontal ⟨1, 15⟩
      | 0, 16 => .horizontal ⟨1, 16⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .horizontal ⟨2, 1⟩
      | 1, 2 => .vertical ⟨1, 2⟩ | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .horizontal ⟨2, 4⟩ | 1, 5 => .vertical ⟨1, 5⟩
      | 1, 6 => .vertical ⟨1, 7⟩ | 1, 7 => .horizontal ⟨2, 7⟩
      | 1, 8 => .horizontal ⟨2, 8⟩ | 1, 9 => .vertical ⟨1, 9⟩
      | 1, 10 => .vertical ⟨1, 10⟩ | 1, 11 => .vertical ⟨1, 11⟩
      | 1, 12 => .vertical ⟨1, 12⟩ | 1, 13 => .vertical ⟨1, 13⟩
      | 1, 14 => .vertical ⟨1, 14⟩ | 1, 15 => .vertical ⟨1, 15⟩
      | 1, 16 => .vertical ⟨1, 16⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .horizontal ⟨3, 1⟩
      | 2, 2 => .vertical ⟨2, 2⟩ | 2, 3 => .vertical ⟨2, 4⟩
      | 2, 4 => .horizontal ⟨3, 4⟩ | 2, 5 => .vertical ⟨2, 5⟩
      | 2, 6 => .vertical ⟨2, 7⟩ | 2, 7 => .horizontal ⟨3, 7⟩
      | 2, 8 => .vertical ⟨2, 8⟩ | 2, 9 => .horizontal ⟨2, 9⟩
      | 2, 10 => .horizontal ⟨2, 10⟩ | 2, 11 => .horizontal ⟨2, 11⟩
      | 2, 12 => .horizontal ⟨2, 12⟩ | 2, 13 => .horizontal ⟨2, 13⟩
      | 2, 14 => .horizontal ⟨2, 14⟩ | 2, 15 => .horizontal ⟨2, 15⟩
      | 2, 16 => .vertical ⟨2, 16⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨4, 1⟩
      | 3, 2 => .vertical ⟨3, 2⟩ | 3, 3 => .vertical ⟨3, 4⟩
      | 3, 4 => .horizontal ⟨4, 4⟩ | 3, 5 => .vertical ⟨3, 5⟩
      | 3, 6 => .vertical ⟨3, 7⟩ | 3, 7 => .vertical ⟨3, 8⟩
      | 3, 8 => .horizontal ⟨4, 8⟩ | 3, 9 => .horizontal ⟨4, 9⟩
      | 3, 10 => .horizontal ⟨4, 10⟩ | 3, 11 => .horizontal ⟨4, 11⟩
      | 3, 12 => .horizontal ⟨4, 12⟩ | 3, 13 => .horizontal ⟨4, 13⟩
      | 3, 14 => .horizontal ⟨4, 14⟩ | 3, 15 => .horizontal ⟨4, 15⟩
      | 3, 16 => .vertical ⟨3, 16⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .horizontal ⟨5, 1⟩
      | 4, 2 => .vertical ⟨4, 2⟩ | 4, 3 => .vertical ⟨4, 4⟩
      | 4, 4 => .vertical ⟨4, 5⟩ | 4, 5 => .horizontal ⟨5, 5⟩
      | 4, 6 => .vertical ⟨4, 7⟩ | 4, 7 => .horizontal ⟨4, 7⟩
      | 4, 8 => .vertical ⟨4, 9⟩ | 4, 9 => .horizontal ⟨5, 9⟩
      | 4, 10 => .vertical ⟨4, 10⟩ | 4, 11 => .vertical ⟨4, 12⟩
      | 4, 12 => .horizontal ⟨5, 12⟩ | 4, 13 => .vertical ⟨4, 13⟩
      | 4, 14 => .vertical ⟨4, 15⟩ | 4, 15 => .horizontal ⟨5, 15⟩
      | 4, 16 => .vertical ⟨4, 16⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .vertical ⟨5, 2⟩
      | 5, 2 => .horizontal ⟨6, 2⟩ | 5, 3 => .vertical ⟨5, 4⟩
      | 5, 4 => .horizontal ⟨5, 4⟩ | 5, 5 => .vertical ⟨5, 6⟩
      | 5, 6 => .horizontal ⟨5, 6⟩ | 5, 7 => .vertical ⟨5, 7⟩
      | 5, 8 => .vertical ⟨5, 9⟩ | 5, 9 => .horizontal ⟨6, 9⟩
      | 5, 10 => .vertical ⟨5, 10⟩ | 5, 11 => .vertical ⟨5, 12⟩
      | 5, 12 => .horizontal ⟨6, 12⟩ | 5, 13 => .vertical ⟨5, 13⟩
      | 5, 14 => .vertical ⟨5, 15⟩ | 5, 15 => .horizontal ⟨6, 15⟩
      | 5, 16 => .vertical ⟨5, 16⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨6, 1⟩
      | 6, 2 => .vertical ⟨6, 3⟩ | 6, 3 => .horizontal ⟨6, 3⟩
      | 6, 4 => .vertical ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 6⟩
      | 6, 6 => .horizontal ⟨6, 6⟩ | 6, 7 => .vertical ⟨6, 7⟩
      | 6, 8 => .vertical ⟨6, 9⟩ | 6, 9 => .horizontal ⟨7, 9⟩
      | 6, 10 => .vertical ⟨6, 10⟩ | 6, 11 => .vertical ⟨6, 12⟩
      | 6, 12 => .horizontal ⟨7, 12⟩ | 6, 13 => .vertical ⟨6, 13⟩
      | 6, 14 => .vertical ⟨6, 15⟩ | 6, 15 => .horizontal ⟨7, 15⟩
      | 6, 16 => .vertical ⟨6, 16⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨8, 1⟩
      | 7, 2 => .vertical ⟨7, 3⟩ | 7, 3 => .horizontal ⟨7, 3⟩
      | 7, 4 => .vertical ⟨7, 4⟩ | 7, 5 => .vertical ⟨7, 6⟩
      | 7, 6 => .horizontal ⟨7, 6⟩ | 7, 7 => .vertical ⟨7, 7⟩
      | 7, 8 => .vertical ⟨7, 9⟩ | 7, 9 => .horizontal ⟨8, 9⟩
      | 7, 10 => .vertical ⟨7, 10⟩ | 7, 11 => .vertical ⟨7, 12⟩
      | 7, 12 => .horizontal ⟨8, 12⟩ | 7, 13 => .vertical ⟨7, 13⟩
      | 7, 14 => .vertical ⟨7, 15⟩ | 7, 15 => .horizontal ⟨8, 15⟩
      | 7, 16 => .vertical ⟨7, 16⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .vertical ⟨8, 2⟩
      | 8, 2 => .horizontal ⟨8, 2⟩ | 8, 3 => .horizontal ⟨8, 3⟩
      | 8, 4 => .vertical ⟨8, 4⟩ | 8, 5 => .vertical ⟨8, 6⟩
      | 8, 6 => .horizontal ⟨8, 6⟩ | 8, 7 => .vertical ⟨8, 7⟩
      | 8, 8 => .vertical ⟨8, 9⟩ | 8, 9 => .horizontal ⟨9, 9⟩
      | 8, 10 => .vertical ⟨8, 10⟩ | 8, 11 => .vertical ⟨8, 12⟩
      | 8, 12 => .horizontal ⟨9, 12⟩ | 8, 13 => .vertical ⟨8, 13⟩
      | 8, 14 => .vertical ⟨8, 15⟩ | 8, 15 => .horizontal ⟨9, 15⟩
      | 8, 16 => .vertical ⟨8, 16⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .horizontal ⟨9, 1⟩
      | 9, 2 => .vertical ⟨9, 2⟩ | 9, 3 => .vertical ⟨9, 4⟩
      | 9, 4 => .horizontal ⟨10, 4⟩ | 9, 5 => .vertical ⟨9, 6⟩
      | 9, 6 => .horizontal ⟨9, 6⟩ | 9, 7 => .vertical ⟨9, 7⟩
      | 9, 8 => .vertical ⟨9, 9⟩ | 9, 9 => .horizontal ⟨10, 9⟩
      | 9, 10 => .vertical ⟨9, 10⟩ | 9, 11 => .vertical ⟨9, 12⟩
      | 9, 12 => .horizontal ⟨10, 12⟩ | 9, 13 => .vertical ⟨9, 13⟩
      | 9, 14 => .vertical ⟨9, 15⟩ | 9, 15 => .horizontal ⟨10, 15⟩
      | 9, 16 => .vertical ⟨9, 16⟩
      | 10, 0 => .vertical ⟨10, 1⟩ | 10, 1 => .horizontal ⟨10, 1⟩
      | 10, 2 => .vertical ⟨10, 2⟩ | 10, 3 => .vertical ⟨10, 4⟩
      | 10, 4 => .vertical ⟨10, 5⟩ | 10, 5 => .horizontal ⟨10, 5⟩
      | 10, 6 => .horizontal ⟨10, 6⟩ | 10, 7 => .vertical ⟨10, 7⟩
      | 10, 8 => .vertical ⟨10, 9⟩ | 10, 9 => .horizontal ⟨11, 9⟩
      | 10, 10 => .vertical ⟨10, 10⟩ | 10, 11 => .vertical ⟨10, 12⟩
      | 10, 12 => .horizontal ⟨11, 12⟩ | 10, 13 => .vertical ⟨10, 13⟩
      | 10, 14 => .vertical ⟨10, 15⟩ | 10, 15 => .horizontal ⟨11, 15⟩
      | 10, 16 => .vertical ⟨10, 16⟩
      | 11, 0 => .vertical ⟨11, 1⟩ | 11, 1 => .horizontal ⟨11, 1⟩
      | 11, 2 => .vertical ⟨11, 2⟩ | 11, 3 => .vertical ⟨11, 4⟩
      | 11, 4 => .horizontal ⟨11, 4⟩ | 11, 5 => .vertical ⟨11, 5⟩
      | 11, 6 => .vertical ⟨11, 7⟩ | 11, 7 => .horizontal ⟨12, 7⟩
      | 11, 8 => .vertical ⟨11, 9⟩ | 11, 9 => .horizontal ⟨12, 9⟩
      | 11, 10 => .vertical ⟨11, 10⟩ | 11, 11 => .vertical ⟨11, 12⟩
      | 11, 12 => .horizontal ⟨12, 12⟩ | 11, 13 => .vertical ⟨11, 13⟩
      | 11, 14 => .vertical ⟨11, 15⟩ | 11, 15 => .horizontal ⟨12, 15⟩
      | 11, 16 => .vertical ⟨11, 16⟩
      | 12, 0 => .vertical ⟨12, 1⟩ | 12, 1 => .horizontal ⟨12, 1⟩
      | 12, 2 => .vertical ⟨12, 2⟩ | 12, 3 => .vertical ⟨12, 4⟩
      | 12, 4 => .horizontal ⟨12, 4⟩ | 12, 5 => .vertical ⟨12, 5⟩
      | 12, 6 => .vertical ⟨12, 7⟩ | 12, 7 => .vertical ⟨12, 8⟩
      | 12, 8 => .horizontal ⟨12, 8⟩ | 12, 9 => .vertical ⟨12, 10⟩
      | 12, 10 => .horizontal ⟨13, 10⟩ | 12, 11 => .vertical ⟨12, 12⟩
      | 12, 12 => .horizontal ⟨13, 12⟩ | 12, 13 => .vertical ⟨12, 13⟩
      | 12, 14 => .vertical ⟨12, 15⟩ | 12, 15 => .horizontal ⟨13, 15⟩
      | 12, 16 => .vertical ⟨12, 16⟩
      | 13, 0 => .vertical ⟨13, 1⟩ | 13, 1 => .horizontal ⟨13, 1⟩
      | 13, 2 => .vertical ⟨13, 2⟩ | 13, 3 => .vertical ⟨13, 4⟩
      | 13, 4 => .horizontal ⟨13, 4⟩ | 13, 5 => .vertical ⟨13, 5⟩
      | 13, 6 => .vertical ⟨13, 7⟩ | 13, 7 => .horizontal ⟨13, 7⟩
      | 13, 8 => .vertical ⟨13, 8⟩ | 13, 9 => .vertical ⟨13, 10⟩
      | 13, 10 => .vertical ⟨13, 11⟩ | 13, 11 => .horizontal ⟨13, 11⟩
      | 13, 12 => .vertical ⟨13, 13⟩ | 13, 13 => .horizontal ⟨14, 13⟩
      | 13, 14 => .horizontal ⟨14, 14⟩ | 13, 15 => .vertical ⟨13, 15⟩
      | 13, 16 => .vertical ⟨13, 16⟩
      | 14, 0 => .vertical ⟨14, 1⟩ | 14, 1 => .horizontal ⟨14, 1⟩
      | 14, 2 => .vertical ⟨14, 2⟩ | 14, 3 => .vertical ⟨14, 4⟩
      | 14, 4 => .horizontal ⟨14, 4⟩ | 14, 5 => .vertical ⟨14, 5⟩
      | 14, 6 => .vertical ⟨14, 7⟩ | 14, 7 => .horizontal ⟨14, 7⟩
      | 14, 8 => .vertical ⟨14, 8⟩ | 14, 9 => .vertical ⟨14, 10⟩
      | 14, 10 => .horizontal ⟨14, 10⟩ | 14, 11 => .vertical ⟨14, 11⟩
      | 14, 12 => .vertical ⟨14, 13⟩ | 14, 13 => .horizontal ⟨15, 13⟩
      | 14, 14 => .vertical ⟨14, 14⟩ | 14, 15 => .horizontal ⟨14, 15⟩
      | 14, 16 => .vertical ⟨14, 16⟩
      | 15, 0 => .vertical ⟨15, 1⟩ | 15, 1 => .horizontal ⟨15, 1⟩
      | 15, 2 => .vertical ⟨15, 2⟩ | 15, 3 => .vertical ⟨15, 4⟩
      | 15, 4 => .horizontal ⟨15, 4⟩ | 15, 5 => .vertical ⟨15, 5⟩
      | 15, 6 => .vertical ⟨15, 7⟩ | 15, 7 => .horizontal ⟨15, 7⟩
      | 15, 8 => .vertical ⟨15, 8⟩ | 15, 9 => .vertical ⟨15, 10⟩
      | 15, 10 => .horizontal ⟨15, 10⟩ | 15, 11 => .vertical ⟨15, 11⟩
      | 15, 12 => .vertical ⟨15, 13⟩ | 15, 13 => .vertical ⟨15, 14⟩
      | 15, 14 => .horizontal ⟨16, 14⟩ | 15, 15 => .horizontal ⟨16, 15⟩
      | 15, 16 => .vertical ⟨15, 16⟩
      | 16, 0 => .vertical ⟨16, 1⟩ | 16, 1 => .horizontal ⟨16, 1⟩
      | 16, 2 => .horizontal ⟨16, 2⟩ | 16, 3 => .horizontal ⟨16, 3⟩
      | 16, 4 => .horizontal ⟨16, 4⟩ | 16, 5 => .horizontal ⟨16, 5⟩
      | 16, 6 => .horizontal ⟨16, 6⟩ | 16, 7 => .horizontal ⟨16, 7⟩
      | 16, 8 => .horizontal ⟨16, 8⟩ | 16, 9 => .horizontal ⟨16, 9⟩
      | 16, 10 => .horizontal ⟨16, 10⟩ | 16, 11 => .horizontal ⟨16, 11⟩
      | 16, 12 => .horizontal ⟨16, 12⟩ | 16, 13 => .horizontal ⟨16, 13⟩
      | 16, 14 => .vertical ⟨16, 15⟩ | 16, 15 => .horizontal ⟨17, 15⟩
      | 16, 16 => .vertical ⟨16, 16⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU18PrimalEdge_adj (e : FiniteU18PrimalEdge)
    (x y : GridFace 18 18) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU18)
    (h₂ : e.primalEndpoints.2 ∈ finiteU18)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU18).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU18_parent_ne (f : GridFace 18 18) (hf : f ≠ .out) :
    f ≠ finiteU18Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> simp [finiteU18Parent]

private theorem finiteU18_parent_edge_data (f : GridFace 18 18) (hf : f ≠ .out) :
    let e := finiteU18ParentEdge f
    e.primalEndpoints.1 ∈ finiteU18 ∧
      e.primalEndpoints.2 ∈ finiteU18 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU18Parent f) := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;>
        norm_num [finiteU18ParentEdge, FiniteU18PrimalEdge.primalEndpoints,
          FiniteU18PrimalEdge.dualEndpoints, finiteU18, finiteU18Selected,
          finiteU18Mask, finiteU18Parent, horizontalPrimalEndpoints,
          verticalPrimalEndpoints, horizontalDualEndpoints, verticalDualEndpoints,
          HasDualEndpoints, Fin.mk.injEq] <;> simp

/-- The explicit ranked parent certificate on all two hundred ninety faces. -/
def finiteU18RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU18) where
  root := .out
  parent := finiteU18Parent
  rank := finiteU18Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU18_parent_edge_data f hf
    exact finiteU18PrimalEdge_adj (finiteU18ParentEdge f) f (finiteU18Parent f)
      (finiteU18_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU18Parent, finiteU18Rank]

theorem finiteU18_compl_card :
    ((Finset.univ : Finset (GridVertex 18 18)) \ finiteU18).card = 124 := by
  have hU : finiteU18.card = 200 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 324 - 200 = 124
  norm_num

/-- One hundred twenty-four vertices can be preserved in the eighteen-by-eighteen grid. -/
theorem oneHundredTwentyFour_le_maxPreserved_eighteen_eighteen :
    124 ≤ maxPreserved 18 18 := by
  rw [← finiteU18_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU18 finiteU18RankedDualCertificate

end GridGraphs
