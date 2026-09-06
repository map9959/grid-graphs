import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for nine rows

This file records the row-mask construction
`[0, 511, 446, 226, 254, 158, 242, 254, 134]`. Connectivity of its U-U
dual is certified by explicit parent, rank, and crossed primal-edge tables.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The mask in row `r` of the nine-by-nine construction. -/
def finiteU9Mask : Nat → Nat
  | 0 => 0
  | 1 => 511
  | 2 => 446
  | 3 => 226
  | 4 => 254
  | 5 => 158
  | 6 => 242
  | 7 => 254
  | 8 => 134
  | _ => 0

/-- Boolean membership in the row-mask construction. -/
private def finiteU9Selected (v : GridVertex 9 9) : Bool :=
  match v.1.val with
  | 0 => false
  | 1 => true
  | 2 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 5 || v.2.val == 7 || v.2.val == 8
  | 3 => v.2.val == 1 || v.2.val == 5 || v.2.val == 6 || v.2.val == 7
  | 4 => 1 ≤ v.2.val && v.2.val ≤ 7
  | 5 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 7
  | 6 => v.2.val == 1 || v.2.val == 4 || v.2.val == 5 ||
      v.2.val == 6 || v.2.val == 7
  | 7 => 1 ≤ v.2.val && v.2.val ≤ 7
  | 8 => v.2.val == 1 || v.2.val == 2 || v.2.val == 7
  | _ => false

/-- The selected vertices with row masks
`[0, 511, 446, 226, 254, 158, 242, 254, 134]`. -/
def finiteU9 : Finset (GridVertex 9 9) :=
  Finset.univ.filter fun v => finiteU9Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU9Parent : GridFace 9 9 → GridFace 9 9
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 1 0 | 0, 1 => .cell 1 1
      | 0, 2 => .cell 1 2 | 0, 3 => .cell 1 3
      | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 1 2
      | 1, 2 => .cell 1 3 | 1, 3 => .cell 1 4
      | 1, 4 => .cell 2 4 | 1, 5 => .cell 1 4
      | 1, 6 => .cell 1 7 | 1, 7 => .out
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 1 1
      | 2, 2 => .cell 1 2 | 2, 3 => .cell 1 3
      | 2, 4 => .cell 2 5 | 2, 5 => .cell 3 5
      | 2, 6 => .cell 2 7 | 2, 7 => .cell 1 7
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 4 1
      | 3, 2 => .cell 4 2 | 3, 3 => .cell 4 3
      | 3, 4 => .cell 3 5 | 3, 5 => .cell 3 6
      | 3, 6 => .cell 2 6 | 3, 7 => .cell 3 6
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 4 2
      | 4, 2 => .cell 4 3 | 4, 3 => .cell 4 4
      | 4, 4 => .cell 3 4 | 4, 5 => .cell 3 5
      | 4, 6 => .cell 3 6 | 4, 7 => .cell 4 6
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 4 1
      | 5, 2 => .cell 4 2 | 5, 3 => .cell 4 3
      | 5, 4 => .cell 5 3 | 5, 5 => .cell 6 5
      | 5, 6 => .cell 6 6 | 5, 7 => .cell 5 6
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 7 1
      | 6, 2 => .cell 7 2 | 6, 3 => .cell 6 4
      | 6, 4 => .cell 5 4 | 6, 5 => .cell 6 4
      | 6, 6 => .cell 6 5 | 6, 7 => .cell 6 6
      | 7, 0 => .cell 7 1 | 7, 1 => .out
      | 7, 2 => .cell 7 1 | 7, 3 => .cell 6 3
      | 7, 4 => .cell 6 4 | 7, 5 => .cell 6 5
      | 7, 6 => .cell 6 6 | 7, 7 => .cell 7 6
      | _, _ => .out

/-- Depths in `finiteU9Parent`, with the outside face at rank zero. -/
def finiteU9Rank : GridFace 9 9 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 13 | 0, 1 => 12 | 0, 2 => 11 | 0, 3 => 10
      | 0, 4 => 9 | 0, 5 => 10 | 0, 6 => 3 | 0, 7 => 2
      | 1, 0 => 12 | 1, 1 => 11 | 1, 2 => 10 | 1, 3 => 9
      | 1, 4 => 8 | 1, 5 => 9 | 1, 6 => 2 | 1, 7 => 1
      | 2, 0 => 13 | 2, 1 => 12 | 2, 2 => 11 | 2, 3 => 10
      | 2, 4 => 7 | 2, 5 => 6 | 2, 6 => 3 | 2, 7 => 2
      | 3, 0 => 12 | 3, 1 => 11 | 3, 2 => 10 | 3, 3 => 9
      | 3, 4 => 6 | 3, 5 => 5 | 3, 6 => 4 | 3, 7 => 5
      | 4, 0 => 11 | 4, 1 => 10 | 4, 2 => 9 | 4, 3 => 8
      | 4, 4 => 7 | 4, 5 => 6 | 4, 6 => 5 | 4, 7 => 6
      | 5, 0 => 12 | 5, 1 => 11 | 5, 2 => 10 | 5, 3 => 9
      | 5, 4 => 10 | 5, 5 => 13 | 5, 6 => 14 | 5, 7 => 15
      | 6, 0 => 3 | 6, 1 => 2 | 6, 2 => 3 | 6, 3 => 12
      | 6, 4 => 11 | 6, 5 => 12 | 6, 6 => 13 | 6, 7 => 14
      | 7, 0 => 2 | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 13
      | 7, 4 => 12 | 7, 5 => 13 | 7, 6 => 14 | 7, 7 => 15
      | _, _ => 0

private inductive FiniteU9PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 9 9)
  | vertical (edge : VerticalGridEdge 9 9)

private def FiniteU9PrimalEdge.primalEndpoints :
    FiniteU9PrimalEdge → GridVertex 9 9 × GridVertex 9 9
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU9PrimalEdge.dualEndpoints :
    FiniteU9PrimalEdge → GridFace 9 9 × GridFace 9 9
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU9ParentEdge : GridFace 9 9 → FiniteU9PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .horizontal ⟨1, 0⟩ | 0, 1 => .horizontal ⟨1, 1⟩
      | 0, 2 => .horizontal ⟨1, 2⟩ | 0, 3 => .horizontal ⟨1, 3⟩
      | 0, 4 => .horizontal ⟨1, 4⟩ | 0, 5 => .horizontal ⟨1, 5⟩
      | 0, 6 => .horizontal ⟨1, 6⟩ | 0, 7 => .horizontal ⟨1, 7⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .vertical ⟨1, 2⟩
      | 1, 2 => .vertical ⟨1, 3⟩ | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .horizontal ⟨2, 4⟩ | 1, 5 => .vertical ⟨1, 5⟩
      | 1, 6 => .vertical ⟨1, 7⟩ | 1, 7 => .vertical ⟨1, 8⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .horizontal ⟨2, 1⟩
      | 2, 2 => .horizontal ⟨2, 2⟩ | 2, 3 => .horizontal ⟨2, 3⟩
      | 2, 4 => .vertical ⟨2, 5⟩ | 2, 5 => .horizontal ⟨3, 5⟩
      | 2, 6 => .vertical ⟨2, 7⟩ | 2, 7 => .horizontal ⟨2, 7⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨4, 1⟩
      | 3, 2 => .horizontal ⟨4, 2⟩ | 3, 3 => .horizontal ⟨4, 3⟩
      | 3, 4 => .vertical ⟨3, 5⟩ | 3, 5 => .vertical ⟨3, 6⟩
      | 3, 6 => .horizontal ⟨3, 6⟩ | 3, 7 => .vertical ⟨3, 7⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .vertical ⟨4, 2⟩
      | 4, 2 => .vertical ⟨4, 3⟩ | 4, 3 => .vertical ⟨4, 4⟩
      | 4, 4 => .horizontal ⟨4, 4⟩ | 4, 5 => .horizontal ⟨4, 5⟩
      | 4, 6 => .horizontal ⟨4, 6⟩ | 4, 7 => .vertical ⟨4, 7⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .horizontal ⟨5, 1⟩
      | 5, 2 => .horizontal ⟨5, 2⟩ | 5, 3 => .horizontal ⟨5, 3⟩
      | 5, 4 => .vertical ⟨5, 4⟩ | 5, 5 => .horizontal ⟨6, 5⟩
      | 5, 6 => .horizontal ⟨6, 6⟩ | 5, 7 => .vertical ⟨5, 7⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨7, 1⟩
      | 6, 2 => .horizontal ⟨7, 2⟩ | 6, 3 => .vertical ⟨6, 4⟩
      | 6, 4 => .horizontal ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 5⟩
      | 6, 6 => .vertical ⟨6, 6⟩ | 6, 7 => .vertical ⟨6, 7⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨8, 1⟩
      | 7, 2 => .vertical ⟨7, 2⟩ | 7, 3 => .horizontal ⟨7, 3⟩
      | 7, 4 => .horizontal ⟨7, 4⟩ | 7, 5 => .horizontal ⟨7, 5⟩
      | 7, 6 => .horizontal ⟨7, 6⟩ | 7, 7 => .vertical ⟨7, 7⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU9PrimalEdge_adj (e : FiniteU9PrimalEdge)
    (x y : GridFace 9 9) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU9)
    (h₂ : e.primalEndpoints.2 ∈ finiteU9)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU9).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU9_parent_ne (f : GridFace 9 9) (hf : f ≠ .out) :
    f ≠ finiteU9Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

set_option maxHeartbeats 3000000 in
private theorem finiteU9_parent_edge_data (f : GridFace 9 9) (hf : f ≠ .out) :
    let e := finiteU9ParentEdge f
    e.primalEndpoints.1 ∈ finiteU9 ∧
      e.primalEndpoints.2 ∈ finiteU9 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU9Parent f) := by
  simp only [finiteU9, Finset.mem_filter, Finset.mem_univ, true_and, HasDualEndpoints]
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

/-- The explicit ranked parent certificate on all sixty-five dual faces. -/
def finiteU9RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU9) where
  root := .out
  parent := finiteU9Parent
  rank := finiteU9Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU9_parent_edge_data f hf
    exact finiteU9PrimalEdge_adj (finiteU9ParentEdge f) f (finiteU9Parent f)
      (finiteU9_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;> decide

theorem finiteU9_compl_card :
    ((Finset.univ : Finset (GridVertex 9 9)) \ finiteU9).card = 34 := by
  have hU : finiteU9.card = 47 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 81 - 47 = 34
  norm_num

/-- Thirty-four vertices can be preserved in the nine-by-nine grid. -/
theorem thirtyFour_le_maxPreserved_nine_nine : 34 ≤ maxPreserved 9 9 := by
  rw [← finiteU9_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU9 finiteU9RankedDualCertificate

end GridGraphs
