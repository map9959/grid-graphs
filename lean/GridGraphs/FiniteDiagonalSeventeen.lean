import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for seventeen rows

This file records the row-mask construction
`[2, 131070, 112350, 63222, 55222, 56758, 62902, 47030, 63158,
55222, 56758, 56758, 62902, 48566, 60854, 65534, 32770]`.
Connectivity of its U-U dual is certified by explicit parent, rank, and crossed
primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 14000000
set_option maxRecDepth 100000

/-- The mask in row `r` of the seventeen-by-seventeen construction. -/
def finiteU17Mask : Nat → Nat
  | 0 => 2 | 1 => 131070 | 2 => 112350 | 3 => 63222
  | 4 => 55222 | 5 => 56758 | 6 => 62902 | 7 => 47030
  | 8 => 63158 | 9 => 55222 | 10 => 56758 | 11 => 56758
  | 12 => 62902 | 13 => 48566 | 14 => 60854 | 15 => 65534
  | 16 => 32770 | _ => 0

private def finiteU17Selected (v : GridVertex 17 17) : Bool :=
  match v.1.val with
  | 0 => v.2.val == 1
  | 1 => 1 ≤ v.2.val
  | 2 => (1 ≤ v.2.val && v.2.val ≤ 4) ||
      (6 ≤ v.2.val && v.2.val ≤ 7) || (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || (15 ≤ v.2.val && v.2.val ≤ 16)
  | 3 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 7) || (9 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 15)
  | 4 | 9 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 10) ||
      v.2.val == 12 || (14 ≤ v.2.val && v.2.val ≤ 15)
  | 5 | 10 | 11 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 12) || (14 ≤ v.2.val && v.2.val ≤ 15)
  | 6 | 12 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 8) ||
      v.2.val == 10 || (12 ≤ v.2.val && v.2.val ≤ 15)
  | 7 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 10) ||
      (12 ≤ v.2.val && v.2.val ≤ 13) || v.2.val == 15
  | 8 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || v.2.val == 7 ||
      (9 ≤ v.2.val && v.2.val ≤ 10) || (12 ≤ v.2.val && v.2.val ≤ 15)
  | 13 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 13) || v.2.val == 15
  | 14 => (1 ≤ v.2.val && v.2.val ≤ 2) ||
      (4 ≤ v.2.val && v.2.val ≤ 5) || (7 ≤ v.2.val && v.2.val ≤ 8) ||
      (10 ≤ v.2.val && v.2.val ≤ 11) || (13 ≤ v.2.val && v.2.val ≤ 15)
  | 15 => 1 ≤ v.2.val && v.2.val ≤ 15
  | 16 => v.2.val == 1 || v.2.val == 15
  | _ => false

/-- The selected vertices with the seventeen specified row masks. -/
def finiteU17 : Finset (GridVertex 17 17) :=
  Finset.univ.filter fun v => finiteU17Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU17Parent : GridFace 17 17 → GridFace 17 17
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 0 1 | 0, 1 => .cell 1 1 | 0, 2 => .cell 1 2 | 0, 3 => .cell 1 3 | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5 | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7 | 0, 8 => .cell 1 8 | 0, 9 => .cell 1 9 | 0, 10 => .cell 1 10 | 0, 11 => .cell 1 11 | 0, 12 => .cell 1 12 | 0, 13 => .cell 1 13 | 0, 14 => .cell 1 14 | 0, 15 => .cell 1 15
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 1 2 | 1, 2 => .cell 1 3 | 1, 3 => .cell 2 3 | 1, 4 => .cell 1 3 | 1, 5 => .cell 1 6 | 1, 6 => .cell 2 6 | 1, 7 => .cell 1 6 | 1, 8 => .cell 1 9 | 1, 9 => .cell 2 9 | 1, 10 => .cell 1 9 | 1, 11 => .cell 1 12 | 1, 12 => .cell 2 12 | 1, 13 => .cell 1 12 | 1, 14 => .cell 1 15 | 1, 15 => .out
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 2 2 | 2, 2 => .cell 1 2 | 2, 3 => .cell 2 4 | 2, 4 => .cell 3 4 | 2, 5 => .cell 2 6 | 2, 6 => .cell 3 6 | 2, 7 => .cell 2 6 | 2, 8 => .cell 2 9 | 2, 9 => .cell 3 9 | 2, 10 => .cell 2 9 | 2, 11 => .cell 2 12 | 2, 12 => .cell 2 13 | 2, 13 => .cell 3 13 | 2, 14 => .cell 2 15 | 2, 15 => .cell 1 15
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 2 1 | 3, 2 => .cell 3 1 | 3, 3 => .cell 3 4 | 3, 4 => .cell 3 5 | 3, 5 => .cell 2 5 | 3, 6 => .cell 3 7 | 3, 7 => .cell 4 7 | 3, 8 => .cell 4 8 | 3, 9 => .cell 3 8 | 3, 10 => .cell 3 9 | 3, 11 => .cell 3 12 | 3, 12 => .cell 2 12 | 3, 13 => .cell 3 14 | 3, 14 => .cell 2 14 | 3, 15 => .cell 3 14
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 3 1 | 4, 2 => .cell 4 1 | 4, 3 => .cell 4 4 | 4, 4 => .cell 3 4 | 4, 5 => .cell 4 4 | 4, 6 => .cell 4 7 | 4, 7 => .cell 5 7 | 4, 8 => .cell 4 7 | 4, 9 => .cell 3 9 | 4, 10 => .cell 4 9 | 4, 11 => .cell 5 11 | 4, 12 => .cell 4 11 | 4, 13 => .cell 4 14 | 4, 14 => .cell 3 14 | 4, 15 => .cell 4 14
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 4 1 | 5, 2 => .cell 5 1 | 5, 3 => .cell 5 4 | 5, 4 => .cell 4 4 | 5, 5 => .cell 5 4 | 5, 6 => .cell 5 7 | 5, 7 => .cell 6 7 | 5, 8 => .cell 5 7 | 5, 9 => .cell 5 10 | 5, 10 => .cell 4 10 | 5, 11 => .cell 5 12 | 5, 12 => .cell 6 12 | 5, 13 => .cell 5 14 | 5, 14 => .cell 4 14 | 5, 15 => .cell 5 14
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 5 1 | 6, 2 => .cell 6 1 | 6, 3 => .cell 6 4 | 6, 4 => .cell 5 4 | 6, 5 => .cell 6 4 | 6, 6 => .cell 6 7 | 6, 7 => .cell 6 8 | 6, 8 => .cell 7 8 | 6, 9 => .cell 7 9 | 6, 10 => .cell 6 9 | 6, 11 => .cell 6 12 | 6, 12 => .cell 6 13 | 6, 13 => .cell 5 13 | 6, 14 => .cell 5 14 | 6, 15 => .cell 6 14
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 6 1 | 7, 2 => .cell 7 1 | 7, 3 => .cell 7 4 | 7, 4 => .cell 6 4 | 7, 5 => .cell 7 4 | 7, 6 => .cell 7 7 | 7, 7 => .cell 6 7 | 7, 8 => .cell 7 9 | 7, 9 => .cell 8 9 | 7, 10 => .cell 7 9 | 7, 11 => .cell 7 12 | 7, 12 => .cell 6 12 | 7, 13 => .cell 7 12 | 7, 14 => .cell 8 14 | 7, 15 => .cell 7 14
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 7 1 | 8, 2 => .cell 8 1 | 8, 3 => .cell 8 4 | 8, 4 => .cell 7 4 | 8, 5 => .cell 8 4 | 8, 6 => .cell 8 7 | 8, 7 => .cell 9 7 | 8, 8 => .cell 8 9 | 8, 9 => .cell 9 9 | 8, 10 => .cell 8 9 | 8, 11 => .cell 8 12 | 8, 12 => .cell 7 12 | 8, 13 => .cell 7 13 | 8, 14 => .cell 8 13 | 8, 15 => .cell 8 14
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 8 1 | 9, 2 => .cell 9 1 | 9, 3 => .cell 9 4 | 9, 4 => .cell 8 4 | 9, 5 => .cell 9 4 | 9, 6 => .cell 9 7 | 9, 7 => .cell 9 8 | 9, 8 => .cell 8 8 | 9, 9 => .cell 9 10 | 9, 10 => .cell 10 10 | 9, 11 => .cell 10 11 | 9, 12 => .cell 9 11 | 9, 13 => .cell 9 14 | 9, 14 => .cell 8 14 | 9, 15 => .cell 9 14
      | 10, 0 => .cell 10 1 | 10, 1 => .cell 9 1 | 10, 2 => .cell 10 1 | 10, 3 => .cell 10 4 | 10, 4 => .cell 9 4 | 10, 5 => .cell 10 4 | 10, 6 => .cell 10 7 | 10, 7 => .cell 9 7 | 10, 8 => .cell 10 7 | 10, 9 => .cell 10 10 | 10, 10 => .cell 10 11 | 10, 11 => .cell 11 11 | 10, 12 => .cell 10 11 | 10, 13 => .cell 10 14 | 10, 14 => .cell 9 14 | 10, 15 => .cell 10 14
      | 11, 0 => .cell 11 1 | 11, 1 => .cell 10 1 | 11, 2 => .cell 11 1 | 11, 3 => .cell 11 4 | 11, 4 => .cell 10 4 | 11, 5 => .cell 11 4 | 11, 6 => .cell 11 7 | 11, 7 => .cell 10 7 | 11, 8 => .cell 11 7 | 11, 9 => .cell 11 10 | 11, 10 => .cell 10 10 | 11, 11 => .cell 11 12 | 11, 12 => .cell 12 12 | 11, 13 => .cell 11 14 | 11, 14 => .cell 10 14 | 11, 15 => .cell 11 14
      | 12, 0 => .cell 12 1 | 12, 1 => .cell 11 1 | 12, 2 => .cell 12 1 | 12, 3 => .cell 12 4 | 12, 4 => .cell 11 4 | 12, 5 => .cell 12 4 | 12, 6 => .cell 12 7 | 12, 7 => .cell 11 7 | 12, 8 => .cell 12 7 | 12, 9 => .cell 12 10 | 12, 10 => .cell 13 10 | 12, 11 => .cell 12 12 | 12, 12 => .cell 12 13 | 12, 13 => .cell 11 13 | 12, 14 => .cell 11 14 | 12, 15 => .cell 12 14
      | 13, 0 => .cell 13 1 | 13, 1 => .cell 12 1 | 13, 2 => .cell 13 1 | 13, 3 => .cell 13 4 | 13, 4 => .cell 12 4 | 13, 5 => .cell 13 4 | 13, 6 => .cell 13 7 | 13, 7 => .cell 12 7 | 13, 8 => .cell 13 7 | 13, 9 => .cell 13 10 | 13, 10 => .cell 13 11 | 13, 11 => .cell 12 11 | 13, 12 => .cell 12 12 | 13, 13 => .cell 13 12 | 13, 14 => .cell 14 14 | 13, 15 => .cell 13 14
      | 14, 0 => .cell 14 1 | 14, 1 => .cell 13 1 | 14, 2 => .cell 14 1 | 14, 3 => .cell 14 4 | 14, 4 => .cell 13 4 | 14, 5 => .cell 14 4 | 14, 6 => .cell 14 7 | 14, 7 => .cell 13 7 | 14, 8 => .cell 14 7 | 14, 9 => .cell 14 10 | 14, 10 => .cell 13 10 | 14, 11 => .cell 14 10 | 14, 12 => .cell 14 13 | 14, 13 => .cell 13 13 | 14, 14 => .cell 14 13 | 14, 15 => .cell 14 14
      | 15, 0 => .cell 15 1 | 15, 1 => .cell 14 1 | 15, 2 => .cell 14 2 | 15, 3 => .cell 14 3 | 15, 4 => .cell 14 4 | 15, 5 => .cell 14 5 | 15, 6 => .cell 14 6 | 15, 7 => .cell 14 7 | 15, 8 => .cell 14 8 | 15, 9 => .cell 14 9 | 15, 10 => .cell 14 10 | 15, 11 => .cell 14 11 | 15, 12 => .cell 14 12 | 15, 13 => .cell 14 13 | 15, 14 => .cell 14 14 | 15, 15 => .cell 15 14
      | _, _ => .out

/-- Depths in `finiteU17Parent`, with the outside face at rank zero. -/
def finiteU17Rank : GridFace 17 17 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 45 | 0, 1 => 44 | 0, 2 => 43 | 0, 3 => 42 | 0, 4 => 43 | 0, 5 => 38 | 0, 6 => 37 | 0, 7 => 38 | 0, 8 => 39 | 0, 9 => 38 | 0, 10 => 39 | 0, 11 => 10 | 0, 12 => 9 | 0, 13 => 10 | 0, 14 => 3 | 0, 15 => 2
      | 1, 0 => 44 | 1, 1 => 43 | 1, 2 => 42 | 1, 3 => 41 | 1, 4 => 42 | 1, 5 => 37 | 1, 6 => 36 | 1, 7 => 37 | 1, 8 => 38 | 1, 9 => 37 | 1, 10 => 38 | 1, 11 => 9 | 1, 12 => 8 | 1, 13 => 9 | 1, 14 => 2 | 1, 15 => 1
      | 2, 0 => 45 | 2, 1 => 44 | 2, 2 => 43 | 2, 3 => 40 | 2, 4 => 39 | 2, 5 => 36 | 2, 6 => 35 | 2, 7 => 36 | 2, 8 => 37 | 2, 9 => 36 | 2, 10 => 37 | 2, 11 => 8 | 2, 12 => 7 | 2, 13 => 6 | 2, 14 => 3 | 2, 15 => 2
      | 3, 0 => 46 | 3, 1 => 45 | 3, 2 => 46 | 3, 3 => 39 | 3, 4 => 38 | 3, 5 => 37 | 3, 6 => 34 | 3, 7 => 33 | 3, 8 => 34 | 3, 9 => 35 | 3, 10 => 36 | 3, 11 => 9 | 3, 12 => 8 | 3, 13 => 5 | 3, 14 => 4 | 3, 15 => 5
      | 4, 0 => 47 | 4, 1 => 46 | 4, 2 => 47 | 4, 3 => 40 | 4, 4 => 39 | 4, 5 => 40 | 4, 6 => 33 | 4, 7 => 32 | 4, 8 => 33 | 4, 9 => 36 | 4, 10 => 37 | 4, 11 => 12 | 4, 12 => 13 | 4, 13 => 6 | 4, 14 => 5 | 4, 15 => 6
      | 5, 0 => 48 | 5, 1 => 47 | 5, 2 => 48 | 5, 3 => 41 | 5, 4 => 40 | 5, 5 => 41 | 5, 6 => 32 | 5, 7 => 31 | 5, 8 => 32 | 5, 9 => 39 | 5, 10 => 38 | 5, 11 => 11 | 5, 12 => 10 | 5, 13 => 7 | 5, 14 => 6 | 5, 15 => 7
      | 6, 0 => 49 | 6, 1 => 48 | 6, 2 => 49 | 6, 3 => 42 | 6, 4 => 41 | 6, 5 => 42 | 6, 6 => 31 | 6, 7 => 30 | 6, 8 => 29 | 6, 9 => 28 | 6, 10 => 29 | 6, 11 => 10 | 6, 12 => 9 | 6, 13 => 8 | 6, 14 => 7 | 6, 15 => 8
      | 7, 0 => 50 | 7, 1 => 49 | 7, 2 => 50 | 7, 3 => 43 | 7, 4 => 42 | 7, 5 => 43 | 7, 6 => 32 | 7, 7 => 31 | 7, 8 => 28 | 7, 9 => 27 | 7, 10 => 28 | 7, 11 => 11 | 7, 12 => 10 | 7, 13 => 11 | 7, 14 => 14 | 7, 15 => 15
      | 8, 0 => 51 | 8, 1 => 50 | 8, 2 => 51 | 8, 3 => 44 | 8, 4 => 43 | 8, 5 => 44 | 8, 6 => 31 | 8, 7 => 30 | 8, 8 => 27 | 8, 9 => 26 | 8, 10 => 27 | 8, 11 => 12 | 8, 12 => 11 | 8, 13 => 12 | 8, 14 => 13 | 8, 15 => 14
      | 9, 0 => 52 | 9, 1 => 51 | 9, 2 => 52 | 9, 3 => 45 | 9, 4 => 44 | 9, 5 => 45 | 9, 6 => 30 | 9, 7 => 29 | 9, 8 => 28 | 9, 9 => 25 | 9, 10 => 24 | 9, 11 => 23 | 9, 12 => 24 | 9, 13 => 15 | 9, 14 => 14 | 9, 15 => 15
      | 10, 0 => 53 | 10, 1 => 52 | 10, 2 => 53 | 10, 3 => 46 | 10, 4 => 45 | 10, 5 => 46 | 10, 6 => 31 | 10, 7 => 30 | 10, 8 => 31 | 10, 9 => 24 | 10, 10 => 23 | 10, 11 => 22 | 10, 12 => 23 | 10, 13 => 16 | 10, 14 => 15 | 10, 15 => 16
      | 11, 0 => 54 | 11, 1 => 53 | 11, 2 => 54 | 11, 3 => 47 | 11, 4 => 46 | 11, 5 => 47 | 11, 6 => 32 | 11, 7 => 31 | 11, 8 => 32 | 11, 9 => 25 | 11, 10 => 24 | 11, 11 => 21 | 11, 12 => 20 | 11, 13 => 17 | 11, 14 => 16 | 11, 15 => 17
      | 12, 0 => 55 | 12, 1 => 54 | 12, 2 => 55 | 12, 3 => 48 | 12, 4 => 47 | 12, 5 => 48 | 12, 6 => 33 | 12, 7 => 32 | 12, 8 => 33 | 12, 9 => 24 | 12, 10 => 23 | 12, 11 => 20 | 12, 12 => 19 | 12, 13 => 18 | 12, 14 => 17 | 12, 15 => 18
      | 13, 0 => 56 | 13, 1 => 55 | 13, 2 => 56 | 13, 3 => 49 | 13, 4 => 48 | 13, 5 => 49 | 13, 6 => 34 | 13, 7 => 33 | 13, 8 => 34 | 13, 9 => 23 | 13, 10 => 22 | 13, 11 => 21 | 13, 12 => 20 | 13, 13 => 21 | 13, 14 => 24 | 13, 15 => 25
      | 14, 0 => 57 | 14, 1 => 56 | 14, 2 => 57 | 14, 3 => 50 | 14, 4 => 49 | 14, 5 => 50 | 14, 6 => 35 | 14, 7 => 34 | 14, 8 => 35 | 14, 9 => 24 | 14, 10 => 23 | 14, 11 => 24 | 14, 12 => 23 | 14, 13 => 22 | 14, 14 => 23 | 14, 15 => 24
      | 15, 0 => 58 | 15, 1 => 57 | 15, 2 => 58 | 15, 3 => 51 | 15, 4 => 50 | 15, 5 => 51 | 15, 6 => 36 | 15, 7 => 35 | 15, 8 => 36 | 15, 9 => 25 | 15, 10 => 24 | 15, 11 => 25 | 15, 12 => 24 | 15, 13 => 23 | 15, 14 => 24 | 15, 15 => 25
      | _, _ => 0

private inductive FiniteU17PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 17 17)
  | vertical (edge : VerticalGridEdge 17 17)

private def FiniteU17PrimalEdge.primalEndpoints :
    FiniteU17PrimalEdge → GridVertex 17 17 × GridVertex 17 17
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU17PrimalEdge.dualEndpoints :
    FiniteU17PrimalEdge → GridFace 17 17 × GridFace 17 17
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU17ParentEdge : GridFace 17 17 → FiniteU17PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .vertical ⟨0, 1⟩ | 0, 1 => .horizontal ⟨1, 1⟩ | 0, 2 => .horizontal ⟨1, 2⟩ | 0, 3 => .horizontal ⟨1, 3⟩ | 0, 4 => .horizontal ⟨1, 4⟩ | 0, 5 => .horizontal ⟨1, 5⟩ | 0, 6 => .horizontal ⟨1, 6⟩ | 0, 7 => .horizontal ⟨1, 7⟩ | 0, 8 => .horizontal ⟨1, 8⟩ | 0, 9 => .horizontal ⟨1, 9⟩ | 0, 10 => .horizontal ⟨1, 10⟩ | 0, 11 => .horizontal ⟨1, 11⟩ | 0, 12 => .horizontal ⟨1, 12⟩ | 0, 13 => .horizontal ⟨1, 13⟩ | 0, 14 => .horizontal ⟨1, 14⟩ | 0, 15 => .horizontal ⟨1, 15⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .vertical ⟨1, 2⟩ | 1, 2 => .vertical ⟨1, 3⟩ | 1, 3 => .horizontal ⟨2, 3⟩ | 1, 4 => .vertical ⟨1, 4⟩ | 1, 5 => .vertical ⟨1, 6⟩ | 1, 6 => .horizontal ⟨2, 6⟩ | 1, 7 => .vertical ⟨1, 7⟩ | 1, 8 => .vertical ⟨1, 9⟩ | 1, 9 => .horizontal ⟨2, 9⟩ | 1, 10 => .vertical ⟨1, 10⟩ | 1, 11 => .vertical ⟨1, 12⟩ | 1, 12 => .horizontal ⟨2, 12⟩ | 1, 13 => .vertical ⟨1, 13⟩ | 1, 14 => .vertical ⟨1, 15⟩ | 1, 15 => .vertical ⟨1, 16⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .vertical ⟨2, 2⟩ | 2, 2 => .horizontal ⟨2, 2⟩ | 2, 3 => .vertical ⟨2, 4⟩ | 2, 4 => .horizontal ⟨3, 4⟩ | 2, 5 => .vertical ⟨2, 6⟩ | 2, 6 => .horizontal ⟨3, 6⟩ | 2, 7 => .vertical ⟨2, 7⟩ | 2, 8 => .vertical ⟨2, 9⟩ | 2, 9 => .horizontal ⟨3, 9⟩ | 2, 10 => .vertical ⟨2, 10⟩ | 2, 11 => .vertical ⟨2, 12⟩ | 2, 12 => .vertical ⟨2, 13⟩ | 2, 13 => .horizontal ⟨3, 13⟩ | 2, 14 => .vertical ⟨2, 15⟩ | 2, 15 => .horizontal ⟨2, 15⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨3, 1⟩ | 3, 2 => .vertical ⟨3, 2⟩ | 3, 3 => .vertical ⟨3, 4⟩ | 3, 4 => .vertical ⟨3, 5⟩ | 3, 5 => .horizontal ⟨3, 5⟩ | 3, 6 => .vertical ⟨3, 7⟩ | 3, 7 => .horizontal ⟨4, 7⟩ | 3, 8 => .horizontal ⟨4, 8⟩ | 3, 9 => .vertical ⟨3, 9⟩ | 3, 10 => .vertical ⟨3, 10⟩ | 3, 11 => .vertical ⟨3, 12⟩ | 3, 12 => .horizontal ⟨3, 12⟩ | 3, 13 => .vertical ⟨3, 14⟩ | 3, 14 => .horizontal ⟨3, 14⟩ | 3, 15 => .vertical ⟨3, 15⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .horizontal ⟨4, 1⟩ | 4, 2 => .vertical ⟨4, 2⟩ | 4, 3 => .vertical ⟨4, 4⟩ | 4, 4 => .horizontal ⟨4, 4⟩ | 4, 5 => .vertical ⟨4, 5⟩ | 4, 6 => .vertical ⟨4, 7⟩ | 4, 7 => .horizontal ⟨5, 7⟩ | 4, 8 => .vertical ⟨4, 8⟩ | 4, 9 => .horizontal ⟨4, 9⟩ | 4, 10 => .vertical ⟨4, 10⟩ | 4, 11 => .horizontal ⟨5, 11⟩ | 4, 12 => .vertical ⟨4, 12⟩ | 4, 13 => .vertical ⟨4, 14⟩ | 4, 14 => .horizontal ⟨4, 14⟩ | 4, 15 => .vertical ⟨4, 15⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .horizontal ⟨5, 1⟩ | 5, 2 => .vertical ⟨5, 2⟩ | 5, 3 => .vertical ⟨5, 4⟩ | 5, 4 => .horizontal ⟨5, 4⟩ | 5, 5 => .vertical ⟨5, 5⟩ | 5, 6 => .vertical ⟨5, 7⟩ | 5, 7 => .horizontal ⟨6, 7⟩ | 5, 8 => .vertical ⟨5, 8⟩ | 5, 9 => .vertical ⟨5, 10⟩ | 5, 10 => .horizontal ⟨5, 10⟩ | 5, 11 => .vertical ⟨5, 12⟩ | 5, 12 => .horizontal ⟨6, 12⟩ | 5, 13 => .vertical ⟨5, 14⟩ | 5, 14 => .horizontal ⟨5, 14⟩ | 5, 15 => .vertical ⟨5, 15⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨6, 1⟩ | 6, 2 => .vertical ⟨6, 2⟩ | 6, 3 => .vertical ⟨6, 4⟩ | 6, 4 => .horizontal ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 5⟩ | 6, 6 => .vertical ⟨6, 7⟩ | 6, 7 => .vertical ⟨6, 8⟩ | 6, 8 => .horizontal ⟨7, 8⟩ | 6, 9 => .horizontal ⟨7, 9⟩ | 6, 10 => .vertical ⟨6, 10⟩ | 6, 11 => .vertical ⟨6, 12⟩ | 6, 12 => .vertical ⟨6, 13⟩ | 6, 13 => .horizontal ⟨6, 13⟩ | 6, 14 => .horizontal ⟨6, 14⟩ | 6, 15 => .vertical ⟨6, 15⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨7, 1⟩ | 7, 2 => .vertical ⟨7, 2⟩ | 7, 3 => .vertical ⟨7, 4⟩ | 7, 4 => .horizontal ⟨7, 4⟩ | 7, 5 => .vertical ⟨7, 5⟩ | 7, 6 => .vertical ⟨7, 7⟩ | 7, 7 => .horizontal ⟨7, 7⟩ | 7, 8 => .vertical ⟨7, 9⟩ | 7, 9 => .horizontal ⟨8, 9⟩ | 7, 10 => .vertical ⟨7, 10⟩ | 7, 11 => .vertical ⟨7, 12⟩ | 7, 12 => .horizontal ⟨7, 12⟩ | 7, 13 => .vertical ⟨7, 13⟩ | 7, 14 => .horizontal ⟨8, 14⟩ | 7, 15 => .vertical ⟨7, 15⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .horizontal ⟨8, 1⟩ | 8, 2 => .vertical ⟨8, 2⟩ | 8, 3 => .vertical ⟨8, 4⟩ | 8, 4 => .horizontal ⟨8, 4⟩ | 8, 5 => .vertical ⟨8, 5⟩ | 8, 6 => .vertical ⟨8, 7⟩ | 8, 7 => .horizontal ⟨9, 7⟩ | 8, 8 => .vertical ⟨8, 9⟩ | 8, 9 => .horizontal ⟨9, 9⟩ | 8, 10 => .vertical ⟨8, 10⟩ | 8, 11 => .vertical ⟨8, 12⟩ | 8, 12 => .horizontal ⟨8, 12⟩ | 8, 13 => .horizontal ⟨8, 13⟩ | 8, 14 => .vertical ⟨8, 14⟩ | 8, 15 => .vertical ⟨8, 15⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .horizontal ⟨9, 1⟩ | 9, 2 => .vertical ⟨9, 2⟩ | 9, 3 => .vertical ⟨9, 4⟩ | 9, 4 => .horizontal ⟨9, 4⟩ | 9, 5 => .vertical ⟨9, 5⟩ | 9, 6 => .vertical ⟨9, 7⟩ | 9, 7 => .vertical ⟨9, 8⟩ | 9, 8 => .horizontal ⟨9, 8⟩ | 9, 9 => .vertical ⟨9, 10⟩ | 9, 10 => .horizontal ⟨10, 10⟩ | 9, 11 => .horizontal ⟨10, 11⟩ | 9, 12 => .vertical ⟨9, 12⟩ | 9, 13 => .vertical ⟨9, 14⟩ | 9, 14 => .horizontal ⟨9, 14⟩ | 9, 15 => .vertical ⟨9, 15⟩
      | 10, 0 => .vertical ⟨10, 1⟩ | 10, 1 => .horizontal ⟨10, 1⟩ | 10, 2 => .vertical ⟨10, 2⟩ | 10, 3 => .vertical ⟨10, 4⟩ | 10, 4 => .horizontal ⟨10, 4⟩ | 10, 5 => .vertical ⟨10, 5⟩ | 10, 6 => .vertical ⟨10, 7⟩ | 10, 7 => .horizontal ⟨10, 7⟩ | 10, 8 => .vertical ⟨10, 8⟩ | 10, 9 => .vertical ⟨10, 10⟩ | 10, 10 => .vertical ⟨10, 11⟩ | 10, 11 => .horizontal ⟨11, 11⟩ | 10, 12 => .vertical ⟨10, 12⟩ | 10, 13 => .vertical ⟨10, 14⟩ | 10, 14 => .horizontal ⟨10, 14⟩ | 10, 15 => .vertical ⟨10, 15⟩
      | 11, 0 => .vertical ⟨11, 1⟩ | 11, 1 => .horizontal ⟨11, 1⟩ | 11, 2 => .vertical ⟨11, 2⟩ | 11, 3 => .vertical ⟨11, 4⟩ | 11, 4 => .horizontal ⟨11, 4⟩ | 11, 5 => .vertical ⟨11, 5⟩ | 11, 6 => .vertical ⟨11, 7⟩ | 11, 7 => .horizontal ⟨11, 7⟩ | 11, 8 => .vertical ⟨11, 8⟩ | 11, 9 => .vertical ⟨11, 10⟩ | 11, 10 => .horizontal ⟨11, 10⟩ | 11, 11 => .vertical ⟨11, 12⟩ | 11, 12 => .horizontal ⟨12, 12⟩ | 11, 13 => .vertical ⟨11, 14⟩ | 11, 14 => .horizontal ⟨11, 14⟩ | 11, 15 => .vertical ⟨11, 15⟩
      | 12, 0 => .vertical ⟨12, 1⟩ | 12, 1 => .horizontal ⟨12, 1⟩ | 12, 2 => .vertical ⟨12, 2⟩ | 12, 3 => .vertical ⟨12, 4⟩ | 12, 4 => .horizontal ⟨12, 4⟩ | 12, 5 => .vertical ⟨12, 5⟩ | 12, 6 => .vertical ⟨12, 7⟩ | 12, 7 => .horizontal ⟨12, 7⟩ | 12, 8 => .vertical ⟨12, 8⟩ | 12, 9 => .vertical ⟨12, 10⟩ | 12, 10 => .horizontal ⟨13, 10⟩ | 12, 11 => .vertical ⟨12, 12⟩ | 12, 12 => .vertical ⟨12, 13⟩ | 12, 13 => .horizontal ⟨12, 13⟩ | 12, 14 => .horizontal ⟨12, 14⟩ | 12, 15 => .vertical ⟨12, 15⟩
      | 13, 0 => .vertical ⟨13, 1⟩ | 13, 1 => .horizontal ⟨13, 1⟩ | 13, 2 => .vertical ⟨13, 2⟩ | 13, 3 => .vertical ⟨13, 4⟩ | 13, 4 => .horizontal ⟨13, 4⟩ | 13, 5 => .vertical ⟨13, 5⟩ | 13, 6 => .vertical ⟨13, 7⟩ | 13, 7 => .horizontal ⟨13, 7⟩ | 13, 8 => .vertical ⟨13, 8⟩ | 13, 9 => .vertical ⟨13, 10⟩ | 13, 10 => .vertical ⟨13, 11⟩ | 13, 11 => .horizontal ⟨13, 11⟩ | 13, 12 => .horizontal ⟨13, 12⟩ | 13, 13 => .vertical ⟨13, 13⟩ | 13, 14 => .horizontal ⟨14, 14⟩ | 13, 15 => .vertical ⟨13, 15⟩
      | 14, 0 => .vertical ⟨14, 1⟩ | 14, 1 => .horizontal ⟨14, 1⟩ | 14, 2 => .vertical ⟨14, 2⟩ | 14, 3 => .vertical ⟨14, 4⟩ | 14, 4 => .horizontal ⟨14, 4⟩ | 14, 5 => .vertical ⟨14, 5⟩ | 14, 6 => .vertical ⟨14, 7⟩ | 14, 7 => .horizontal ⟨14, 7⟩ | 14, 8 => .vertical ⟨14, 8⟩ | 14, 9 => .vertical ⟨14, 10⟩ | 14, 10 => .horizontal ⟨14, 10⟩ | 14, 11 => .vertical ⟨14, 11⟩ | 14, 12 => .vertical ⟨14, 13⟩ | 14, 13 => .horizontal ⟨14, 13⟩ | 14, 14 => .vertical ⟨14, 14⟩ | 14, 15 => .vertical ⟨14, 15⟩
      | 15, 0 => .vertical ⟨15, 1⟩ | 15, 1 => .horizontal ⟨15, 1⟩ | 15, 2 => .horizontal ⟨15, 2⟩ | 15, 3 => .horizontal ⟨15, 3⟩ | 15, 4 => .horizontal ⟨15, 4⟩ | 15, 5 => .horizontal ⟨15, 5⟩ | 15, 6 => .horizontal ⟨15, 6⟩ | 15, 7 => .horizontal ⟨15, 7⟩ | 15, 8 => .horizontal ⟨15, 8⟩ | 15, 9 => .horizontal ⟨15, 9⟩ | 15, 10 => .horizontal ⟨15, 10⟩ | 15, 11 => .horizontal ⟨15, 11⟩ | 15, 12 => .horizontal ⟨15, 12⟩ | 15, 13 => .horizontal ⟨15, 13⟩ | 15, 14 => .horizontal ⟨15, 14⟩ | 15, 15 => .vertical ⟨15, 15⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU17PrimalEdge_adj (e : FiniteU17PrimalEdge)
    (x y : GridFace 17 17) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU17)
    (h₂ : e.primalEndpoints.2 ∈ finiteU17)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU17).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU17_parent_ne (f : GridFace 17 17) (hf : f ≠ .out) :
    f ≠ finiteU17Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

private theorem finiteU17_parent_edge_data (f : GridFace 17 17) (hf : f ≠ .out) :
    let e := finiteU17ParentEdge f
    e.primalEndpoints.1 ∈ finiteU17 ∧
      e.primalEndpoints.2 ∈ finiteU17 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU17Parent f) := by
  simp only [finiteU17, Finset.mem_filter, Finset.mem_univ, true_and, HasDualEndpoints]
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

/-- The explicit ranked parent certificate on all two hundred fifty-seven faces. -/
def finiteU17RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU17) where
  root := .out
  parent := finiteU17Parent
  rank := finiteU17Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU17_parent_edge_data f hf
    exact finiteU17PrimalEdge_adj (finiteU17ParentEdge f) f (finiteU17Parent f)
      (finiteU17_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;> decide

theorem finiteU17_compl_card :
    ((Finset.univ : Finset (GridVertex 17 17)) \ finiteU17).card = 110 := by
  have hU : finiteU17.card = 179 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 289 - 179 = 110
  norm_num

/-- One hundred ten vertices can be preserved in the seventeen-by-seventeen grid. -/
theorem oneHundredTen_le_maxPreserved_seventeen_seventeen :
    110 ≤ maxPreserved 17 17 := by
  rw [← finiteU17_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU17 finiteU17RankedDualCertificate

end GridGraphs
