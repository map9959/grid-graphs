import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for twelve rows

This file records the row-mask construction
`[0, 4095, 3582, 1794, 2046, 1278, 1922, 2046, 1142, 2014, 2046, 1026]`.
Connectivity of its U-U dual is certified by explicit parent, rank, and crossed
primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The mask in row `r` of the twelve-by-twelve construction. -/
def finiteU12Mask : Nat → Nat
  | 0 => 0
  | 1 => 4095
  | 2 => 3582
  | 3 => 1794
  | 4 => 2046
  | 5 => 1278
  | 6 => 1922
  | 7 => 2046
  | 8 => 1142
  | 9 => 2014
  | 10 => 2046
  | 11 => 1026
  | _ => 0

/-- Boolean membership in the row-mask construction. -/
private def finiteU12Selected (v : GridVertex 12 12) : Bool :=
  match v.1.val with
  | 0 => false
  | 1 => true
  | 2 => (1 ≤ v.2.val && v.2.val ≤ 8) || 10 ≤ v.2.val
  | 3 => v.2.val == 1 || (8 ≤ v.2.val && v.2.val ≤ 10)
  | 4 => 1 ≤ v.2.val && v.2.val ≤ 10
  | 5 => (1 ≤ v.2.val && v.2.val ≤ 7) || v.2.val == 10
  | 6 => v.2.val == 1 || (7 ≤ v.2.val && v.2.val ≤ 10)
  | 7 => 1 ≤ v.2.val && v.2.val ≤ 10
  | 8 => v.2.val == 1 || v.2.val == 2 ||
      (4 ≤ v.2.val && v.2.val ≤ 6) || v.2.val == 10
  | 9 => (1 ≤ v.2.val && v.2.val ≤ 4) ||
      (6 ≤ v.2.val && v.2.val ≤ 10)
  | 10 => 1 ≤ v.2.val && v.2.val ≤ 10
  | 11 => v.2.val == 1 || v.2.val == 10
  | _ => false

/-- The selected vertices with row masks
`[0, 4095, 3582, 1794, 2046, 1278, 1922, 2046, 1142, 2014, 2046, 1026]`. -/
def finiteU12 : Finset (GridVertex 12 12) :=
  Finset.univ.filter fun v => finiteU12Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU12Parent : GridFace 12 12 → GridFace 12 12
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 1 0 | 0, 1 => .cell 1 1
      | 0, 2 => .cell 1 2 | 0, 3 => .cell 1 3
      | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7
      | 0, 8 => .cell 1 8 | 0, 9 => .cell 1 9
      | 0, 10 => .cell 1 10
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 1 2
      | 1, 2 => .cell 1 3 | 1, 3 => .cell 1 4
      | 1, 4 => .cell 1 5 | 1, 5 => .cell 1 6
      | 1, 6 => .cell 1 7 | 1, 7 => .cell 2 7
      | 1, 8 => .cell 1 7 | 1, 9 => .cell 1 10 | 1, 10 => .out
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 1 1
      | 2, 2 => .cell 1 2 | 2, 3 => .cell 1 3
      | 2, 4 => .cell 1 4 | 2, 5 => .cell 1 5
      | 2, 6 => .cell 1 6 | 2, 7 => .cell 2 8
      | 2, 8 => .cell 3 8 | 2, 9 => .cell 2 10
      | 2, 10 => .cell 1 10
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 4 1
      | 3, 2 => .cell 4 2 | 3, 3 => .cell 4 3
      | 3, 4 => .cell 4 4 | 3, 5 => .cell 4 5
      | 3, 6 => .cell 4 6 | 3, 7 => .cell 3 8
      | 3, 8 => .cell 3 9 | 3, 9 => .cell 2 9
      | 3, 10 => .cell 3 9
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 4 2
      | 4, 2 => .cell 4 3 | 4, 3 => .cell 4 4
      | 4, 4 => .cell 4 5 | 4, 5 => .cell 4 6
      | 4, 6 => .cell 4 7 | 4, 7 => .cell 3 7
      | 4, 8 => .cell 3 8 | 4, 9 => .cell 3 9
      | 4, 10 => .cell 4 9
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 4 1
      | 5, 2 => .cell 4 2 | 5, 3 => .cell 4 3
      | 5, 4 => .cell 4 4 | 5, 5 => .cell 4 5
      | 5, 6 => .cell 4 6 | 5, 7 => .cell 5 6
      | 5, 8 => .cell 6 8 | 5, 9 => .cell 6 9
      | 5, 10 => .cell 5 9
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 7 1
      | 6, 2 => .cell 7 2 | 6, 3 => .cell 7 3
      | 6, 4 => .cell 7 4 | 6, 5 => .cell 7 5
      | 6, 6 => .cell 6 7 | 6, 7 => .cell 5 7
      | 6, 8 => .cell 6 7 | 6, 9 => .cell 6 8
      | 6, 10 => .cell 6 9
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 8 1
      | 7, 2 => .cell 7 1 | 7, 3 => .cell 7 4
      | 7, 4 => .cell 7 5 | 7, 5 => .cell 7 6
      | 7, 6 => .cell 6 6 | 7, 7 => .cell 6 7
      | 7, 8 => .cell 6 8 | 7, 9 => .cell 6 9
      | 7, 10 => .cell 7 9
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 8 2
      | 8, 2 => .cell 9 2 | 8, 3 => .cell 8 4
      | 8, 4 => .cell 7 4 | 8, 5 => .cell 7 5
      | 8, 6 => .cell 8 5 | 8, 7 => .cell 9 7
      | 8, 8 => .cell 9 8 | 8, 9 => .cell 9 9
      | 8, 10 => .cell 8 9
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 9 2
      | 9, 2 => .cell 9 3 | 9, 3 => .cell 8 3
      | 9, 4 => .cell 9 3 | 9, 5 => .cell 9 6
      | 9, 6 => .cell 8 6 | 9, 7 => .cell 9 6
      | 9, 8 => .cell 9 7 | 9, 9 => .cell 9 8
      | 9, 10 => .cell 9 9
      | 10, 0 => .cell 10 1 | 10, 1 => .cell 9 1
      | 10, 2 => .cell 9 2 | 10, 3 => .cell 9 3
      | 10, 4 => .cell 9 4 | 10, 5 => .cell 9 5
      | 10, 6 => .cell 9 6 | 10, 7 => .cell 9 7
      | 10, 8 => .cell 9 8 | 10, 9 => .cell 9 9
      | 10, 10 => .cell 10 9
      | _, _ => .out

/-- Depths in `finiteU12Parent`, with the outside face at rank zero. -/
def finiteU12Rank : GridFace 12 12 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 16 | 0, 1 => 15 | 0, 2 => 14 | 0, 3 => 13
      | 0, 4 => 12 | 0, 5 => 11 | 0, 6 => 10 | 0, 7 => 9
      | 0, 8 => 10 | 0, 9 => 3 | 0, 10 => 2
      | 1, 0 => 15 | 1, 1 => 14 | 1, 2 => 13 | 1, 3 => 12
      | 1, 4 => 11 | 1, 5 => 10 | 1, 6 => 9 | 1, 7 => 8
      | 1, 8 => 9 | 1, 9 => 2 | 1, 10 => 1
      | 2, 0 => 16 | 2, 1 => 15 | 2, 2 => 14 | 2, 3 => 13
      | 2, 4 => 12 | 2, 5 => 11 | 2, 6 => 10 | 2, 7 => 7
      | 2, 8 => 6 | 2, 9 => 3 | 2, 10 => 2
      | 3, 0 => 15 | 3, 1 => 14 | 3, 2 => 13 | 3, 3 => 12
      | 3, 4 => 11 | 3, 5 => 10 | 3, 6 => 9 | 3, 7 => 6
      | 3, 8 => 5 | 3, 9 => 4 | 3, 10 => 5
      | 4, 0 => 14 | 4, 1 => 13 | 4, 2 => 12 | 4, 3 => 11
      | 4, 4 => 10 | 4, 5 => 9 | 4, 6 => 8 | 4, 7 => 7
      | 4, 8 => 6 | 4, 9 => 5 | 4, 10 => 6
      | 5, 0 => 15 | 5, 1 => 14 | 5, 2 => 13 | 5, 3 => 12
      | 5, 4 => 11 | 5, 5 => 10 | 5, 6 => 9 | 5, 7 => 10
      | 5, 8 => 13 | 5, 9 => 14 | 5, 10 => 15
      | 6, 0 => 24 | 6, 1 => 23 | 6, 2 => 24 | 6, 3 => 17
      | 6, 4 => 16 | 6, 5 => 15 | 6, 6 => 12 | 6, 7 => 11
      | 6, 8 => 12 | 6, 9 => 13 | 6, 10 => 14
      | 7, 0 => 23 | 7, 1 => 22 | 7, 2 => 23 | 7, 3 => 16
      | 7, 4 => 15 | 7, 5 => 14 | 7, 6 => 13 | 7, 7 => 12
      | 7, 8 => 13 | 7, 9 => 14 | 7, 10 => 15
      | 8, 0 => 22 | 8, 1 => 21 | 8, 2 => 20 | 8, 3 => 17
      | 8, 4 => 16 | 8, 5 => 15 | 8, 6 => 16 | 8, 7 => 19
      | 8, 8 => 20 | 8, 9 => 21 | 8, 10 => 22
      | 9, 0 => 21 | 9, 1 => 20 | 9, 2 => 19 | 9, 3 => 18
      | 9, 4 => 19 | 9, 5 => 18 | 9, 6 => 17 | 9, 7 => 18
      | 9, 8 => 19 | 9, 9 => 20 | 9, 10 => 21
      | 10, 0 => 22 | 10, 1 => 21 | 10, 2 => 20 | 10, 3 => 19
      | 10, 4 => 20 | 10, 5 => 19 | 10, 6 => 18 | 10, 7 => 19
      | 10, 8 => 20 | 10, 9 => 21 | 10, 10 => 22
      | _, _ => 0

private inductive FiniteU12PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 12 12)
  | vertical (edge : VerticalGridEdge 12 12)

private def FiniteU12PrimalEdge.primalEndpoints :
    FiniteU12PrimalEdge → GridVertex 12 12 × GridVertex 12 12
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU12PrimalEdge.dualEndpoints :
    FiniteU12PrimalEdge → GridFace 12 12 × GridFace 12 12
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU12ParentEdge : GridFace 12 12 → FiniteU12PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .horizontal ⟨1, 0⟩ | 0, 1 => .horizontal ⟨1, 1⟩
      | 0, 2 => .horizontal ⟨1, 2⟩ | 0, 3 => .horizontal ⟨1, 3⟩
      | 0, 4 => .horizontal ⟨1, 4⟩ | 0, 5 => .horizontal ⟨1, 5⟩
      | 0, 6 => .horizontal ⟨1, 6⟩ | 0, 7 => .horizontal ⟨1, 7⟩
      | 0, 8 => .horizontal ⟨1, 8⟩ | 0, 9 => .horizontal ⟨1, 9⟩
      | 0, 10 => .horizontal ⟨1, 10⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .vertical ⟨1, 2⟩
      | 1, 2 => .vertical ⟨1, 3⟩ | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .vertical ⟨1, 5⟩ | 1, 5 => .vertical ⟨1, 6⟩
      | 1, 6 => .vertical ⟨1, 7⟩ | 1, 7 => .horizontal ⟨2, 7⟩
      | 1, 8 => .vertical ⟨1, 8⟩ | 1, 9 => .vertical ⟨1, 10⟩
      | 1, 10 => .vertical ⟨1, 11⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .horizontal ⟨2, 1⟩
      | 2, 2 => .horizontal ⟨2, 2⟩ | 2, 3 => .horizontal ⟨2, 3⟩
      | 2, 4 => .horizontal ⟨2, 4⟩ | 2, 5 => .horizontal ⟨2, 5⟩
      | 2, 6 => .horizontal ⟨2, 6⟩ | 2, 7 => .vertical ⟨2, 8⟩
      | 2, 8 => .horizontal ⟨3, 8⟩ | 2, 9 => .vertical ⟨2, 10⟩
      | 2, 10 => .horizontal ⟨2, 10⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨4, 1⟩
      | 3, 2 => .horizontal ⟨4, 2⟩ | 3, 3 => .horizontal ⟨4, 3⟩
      | 3, 4 => .horizontal ⟨4, 4⟩ | 3, 5 => .horizontal ⟨4, 5⟩
      | 3, 6 => .horizontal ⟨4, 6⟩ | 3, 7 => .vertical ⟨3, 8⟩
      | 3, 8 => .vertical ⟨3, 9⟩ | 3, 9 => .horizontal ⟨3, 9⟩
      | 3, 10 => .vertical ⟨3, 10⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .vertical ⟨4, 2⟩
      | 4, 2 => .vertical ⟨4, 3⟩ | 4, 3 => .vertical ⟨4, 4⟩
      | 4, 4 => .vertical ⟨4, 5⟩ | 4, 5 => .vertical ⟨4, 6⟩
      | 4, 6 => .vertical ⟨4, 7⟩ | 4, 7 => .horizontal ⟨4, 7⟩
      | 4, 8 => .horizontal ⟨4, 8⟩ | 4, 9 => .horizontal ⟨4, 9⟩
      | 4, 10 => .vertical ⟨4, 10⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .horizontal ⟨5, 1⟩
      | 5, 2 => .horizontal ⟨5, 2⟩ | 5, 3 => .horizontal ⟨5, 3⟩
      | 5, 4 => .horizontal ⟨5, 4⟩ | 5, 5 => .horizontal ⟨5, 5⟩
      | 5, 6 => .horizontal ⟨5, 6⟩ | 5, 7 => .vertical ⟨5, 7⟩
      | 5, 8 => .horizontal ⟨6, 8⟩ | 5, 9 => .horizontal ⟨6, 9⟩
      | 5, 10 => .vertical ⟨5, 10⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨7, 1⟩
      | 6, 2 => .horizontal ⟨7, 2⟩ | 6, 3 => .horizontal ⟨7, 3⟩
      | 6, 4 => .horizontal ⟨7, 4⟩ | 6, 5 => .horizontal ⟨7, 5⟩
      | 6, 6 => .vertical ⟨6, 7⟩ | 6, 7 => .horizontal ⟨6, 7⟩
      | 6, 8 => .vertical ⟨6, 8⟩ | 6, 9 => .vertical ⟨6, 9⟩
      | 6, 10 => .vertical ⟨6, 10⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨8, 1⟩
      | 7, 2 => .vertical ⟨7, 2⟩ | 7, 3 => .vertical ⟨7, 4⟩
      | 7, 4 => .vertical ⟨7, 5⟩ | 7, 5 => .vertical ⟨7, 6⟩
      | 7, 6 => .horizontal ⟨7, 6⟩ | 7, 7 => .horizontal ⟨7, 7⟩
      | 7, 8 => .horizontal ⟨7, 8⟩ | 7, 9 => .horizontal ⟨7, 9⟩
      | 7, 10 => .vertical ⟨7, 10⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .vertical ⟨8, 2⟩
      | 8, 2 => .horizontal ⟨9, 2⟩ | 8, 3 => .vertical ⟨8, 4⟩
      | 8, 4 => .horizontal ⟨8, 4⟩ | 8, 5 => .horizontal ⟨8, 5⟩
      | 8, 6 => .vertical ⟨8, 6⟩ | 8, 7 => .horizontal ⟨9, 7⟩
      | 8, 8 => .horizontal ⟨9, 8⟩ | 8, 9 => .horizontal ⟨9, 9⟩
      | 8, 10 => .vertical ⟨8, 10⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .vertical ⟨9, 2⟩
      | 9, 2 => .vertical ⟨9, 3⟩ | 9, 3 => .horizontal ⟨9, 3⟩
      | 9, 4 => .vertical ⟨9, 4⟩ | 9, 5 => .vertical ⟨9, 6⟩
      | 9, 6 => .horizontal ⟨9, 6⟩ | 9, 7 => .vertical ⟨9, 7⟩
      | 9, 8 => .vertical ⟨9, 8⟩ | 9, 9 => .vertical ⟨9, 9⟩
      | 9, 10 => .vertical ⟨9, 10⟩
      | 10, 0 => .vertical ⟨10, 1⟩ | 10, 1 => .horizontal ⟨10, 1⟩
      | 10, 2 => .horizontal ⟨10, 2⟩ | 10, 3 => .horizontal ⟨10, 3⟩
      | 10, 4 => .horizontal ⟨10, 4⟩ | 10, 5 => .horizontal ⟨10, 5⟩
      | 10, 6 => .horizontal ⟨10, 6⟩ | 10, 7 => .horizontal ⟨10, 7⟩
      | 10, 8 => .horizontal ⟨10, 8⟩ | 10, 9 => .horizontal ⟨10, 9⟩
      | 10, 10 => .vertical ⟨10, 10⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU12PrimalEdge_adj (e : FiniteU12PrimalEdge)
    (x y : GridFace 12 12) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU12)
    (h₂ : e.primalEndpoints.2 ∈ finiteU12)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU12).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

set_option maxHeartbeats 1000000 in
private theorem finiteU12_parent_ne (f : GridFace 12 12) (hf : f ≠ .out) :
    f ≠ finiteU12Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> simp [finiteU12Parent]

set_option maxHeartbeats 5000000 in
private theorem finiteU12_parent_edge_data (f : GridFace 12 12) (hf : f ≠ .out) :
    let e := finiteU12ParentEdge f
    e.primalEndpoints.1 ∈ finiteU12 ∧
      e.primalEndpoints.2 ∈ finiteU12 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU12Parent f) := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;>
        norm_num [finiteU12ParentEdge, FiniteU12PrimalEdge.primalEndpoints,
          FiniteU12PrimalEdge.dualEndpoints, finiteU12, finiteU12Selected,
          finiteU12Parent, horizontalPrimalEndpoints, verticalPrimalEndpoints,
          horizontalDualEndpoints, verticalDualEndpoints, HasDualEndpoints,
          Fin.mk.injEq] <;> simp

set_option maxHeartbeats 1000000 in
/-- The explicit ranked parent certificate on all one hundred twenty-two faces. -/
def finiteU12RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU12) where
  root := .out
  parent := finiteU12Parent
  rank := finiteU12Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU12_parent_edge_data f hf
    exact finiteU12PrimalEdge_adj (finiteU12ParentEdge f) f (finiteU12Parent f)
      (finiteU12_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU12Parent, finiteU12Rank]

set_option maxRecDepth 2000 in
theorem finiteU12_compl_card :
    ((Finset.univ : Finset (GridVertex 12 12)) \ finiteU12).card = 58 := by
  have hU : finiteU12.card = 86 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 144 - 86 = 58
  norm_num

/-- Fifty-eight vertices can be preserved in the twelve-by-twelve grid. -/
theorem fiftyEight_le_maxPreserved_twelve_twelve : 58 ≤ maxPreserved 12 12 := by
  rw [← finiteU12_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU12 finiteU12RankedDualCertificate

end GridGraphs
