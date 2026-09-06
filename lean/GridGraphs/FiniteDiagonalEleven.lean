import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for eleven rows

This file records the row-mask construction
`[2, 2046, 1014, 542, 1018, 878, 894, 962, 1790, 2046, 2]`.
Connectivity of its U-U dual is certified by an explicit parent edge and rank
for each of the one hundred bounded faces.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The mask in row `r` of the eleven-by-eleven construction. -/
def finiteU11Mask : Nat → Nat
  | 0 => 2
  | 1 => 2046
  | 2 => 1014
  | 3 => 542
  | 4 => 1018
  | 5 => 878
  | 6 => 894
  | 7 => 962
  | 8 => 1790
  | 9 => 2046
  | 10 => 2
  | _ => 0

private def finiteU11Selected (v : GridVertex 11 11) : Bool :=
  match v.1.val with
  | 0 => v.2.val == 1
  | 1 => 1 ≤ v.2.val
  | 2 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 8 || v.2.val == 9
  | 3 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 9
  | 4 => v.2.val == 1 || v.2.val == 3 || v.2.val == 4 ||
      v.2.val == 5 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 8 || v.2.val == 9
  | 5 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 5 || v.2.val == 6 || v.2.val == 8 || v.2.val == 9
  | 6 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
      v.2.val == 4 || v.2.val == 5 || v.2.val == 6 ||
      v.2.val == 8 || v.2.val == 9
  | 7 => v.2.val == 1 || v.2.val == 6 || v.2.val == 7 ||
      v.2.val == 8 || v.2.val == 9
  | 8 => (1 ≤ v.2.val && v.2.val ≤ 7) || v.2.val == 9 || v.2.val == 10
  | 9 => 1 ≤ v.2.val
  | 10 => v.2.val == 1
  | _ => false

/-- The selected vertices with row masks
`[2, 2046, 1014, 542, 1018, 878, 894, 962, 1790, 2046, 2]`. -/
def finiteU11 : Finset (GridVertex 11 11) :=
  Finset.univ.filter fun v => finiteU11Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU11Parent : GridFace 11 11 → GridFace 11 11
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 0 1 | 0, 1 => .cell 1 1
      | 0, 2 => .cell 1 2 | 0, 3 => .cell 1 3
      | 0, 4 => .cell 1 4 | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6 | 0, 7 => .cell 1 7
      | 0, 8 => .cell 1 8 | 0, 9 => .cell 1 9
      | 1, 0 => .cell 1 1 | 1, 1 => .cell 2 1
      | 1, 2 => .cell 1 1 | 1, 3 => .cell 1 4
      | 1, 4 => .cell 2 4 | 1, 5 => .cell 1 4
      | 1, 6 => .cell 1 5 | 1, 7 => .cell 1 6
      | 1, 8 => .cell 1 7 | 1, 9 => .cell 1 8
      | 2, 0 => .cell 2 1 | 2, 1 => .cell 2 2
      | 2, 2 => .cell 3 2 | 2, 3 => .cell 3 3
      | 2, 4 => .cell 2 3 | 2, 5 => .cell 1 5
      | 2, 6 => .cell 1 6 | 2, 7 => .cell 1 7
      | 2, 8 => .cell 1 8 | 2, 9 => .cell 2 8
      | 3, 0 => .cell 3 1 | 3, 1 => .cell 2 1
      | 3, 2 => .cell 3 3 | 3, 3 => .cell 3 4
      | 3, 4 => .cell 4 4 | 3, 5 => .cell 4 5
      | 3, 6 => .cell 4 6 | 3, 7 => .cell 4 7
      | 3, 8 => .cell 4 8 | 3, 9 => .cell 3 8
      | 4, 0 => .cell 4 1 | 4, 1 => .cell 5 1
      | 4, 2 => .cell 4 3 | 4, 3 => .cell 3 3
      | 4, 4 => .cell 4 5 | 4, 5 => .cell 5 5
      | 4, 6 => .cell 4 5 | 4, 7 => .cell 4 8
      | 4, 8 => .cell 5 8 | 4, 9 => .cell 4 8
      | 5, 0 => .cell 5 1 | 5, 1 => .cell 5 2
      | 5, 2 => .cell 4 2 | 5, 3 => .cell 5 2
      | 5, 4 => .cell 5 5 | 5, 5 => .cell 6 5
      | 5, 6 => .cell 5 5 | 5, 7 => .cell 5 8
      | 5, 8 => .cell 6 8 | 5, 9 => .cell 5 8
      | 6, 0 => .cell 6 1 | 6, 1 => .cell 5 1
      | 6, 2 => .cell 5 2 | 6, 3 => .cell 5 3
      | 6, 4 => .cell 5 4 | 6, 5 => .cell 6 6
      | 6, 6 => .cell 7 6 | 6, 7 => .cell 6 8
      | 6, 8 => .cell 7 8 | 6, 9 => .cell 6 8
      | 7, 0 => .cell 7 1 | 7, 1 => .cell 8 1
      | 7, 2 => .cell 8 2 | 7, 3 => .cell 8 3
      | 7, 4 => .cell 8 4 | 7, 5 => .cell 7 6
      | 7, 6 => .cell 7 7 | 7, 7 => .cell 6 7
      | 7, 8 => .cell 7 9 | 7, 9 => .cell 8 9
      | 8, 0 => .cell 8 1 | 8, 1 => .cell 8 2
      | 8, 2 => .cell 8 3 | 8, 3 => .cell 8 4
      | 8, 4 => .cell 8 5 | 8, 5 => .cell 8 6
      | 8, 6 => .cell 7 6 | 8, 7 => .cell 8 6
      | 8, 8 => .cell 8 9 | 8, 9 => .out
      | 9, 0 => .cell 9 1 | 9, 1 => .cell 8 1
      | 9, 2 => .cell 8 2 | 9, 3 => .cell 8 3
      | 9, 4 => .cell 8 4 | 9, 5 => .cell 8 5
      | 9, 6 => .cell 8 6 | 9, 7 => .cell 8 7
      | 9, 8 => .cell 8 8 | 9, 9 => .cell 8 9
      | _, _ => .out

/-- Depths in `finiteU11Parent`, with the outside face at rank zero. -/
def finiteU11Rank : GridFace 11 11 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 20 | 0, 1 => 19 | 0, 2 => 20 | 0, 3 => 19 | 0, 4 => 18
      | 0, 5 => 19 | 0, 6 => 20 | 0, 7 => 21 | 0, 8 => 22 | 0, 9 => 23
      | 1, 0 => 19 | 1, 1 => 18 | 1, 2 => 19 | 1, 3 => 18 | 1, 4 => 17
      | 1, 5 => 18 | 1, 6 => 19 | 1, 7 => 20 | 1, 8 => 21 | 1, 9 => 22
      | 2, 0 => 18 | 2, 1 => 17 | 2, 2 => 16 | 2, 3 => 15 | 2, 4 => 16
      | 2, 5 => 19 | 2, 6 => 20 | 2, 7 => 21 | 2, 8 => 22 | 2, 9 => 23
      | 3, 0 => 19 | 3, 1 => 18 | 3, 2 => 15 | 3, 3 => 14 | 3, 4 => 13
      | 3, 5 => 12 | 3, 6 => 13 | 3, 7 => 8 | 3, 8 => 7 | 3, 9 => 8
      | 4, 0 => 20 | 4, 1 => 19 | 4, 2 => 16 | 4, 3 => 15 | 4, 4 => 12
      | 4, 5 => 11 | 4, 6 => 12 | 4, 7 => 7 | 4, 8 => 6 | 4, 9 => 7
      | 5, 0 => 19 | 5, 1 => 18 | 5, 2 => 17 | 5, 3 => 18 | 5, 4 => 11
      | 5, 5 => 10 | 5, 6 => 11 | 5, 7 => 6 | 5, 8 => 5 | 5, 9 => 6
      | 6, 0 => 20 | 6, 1 => 19 | 6, 2 => 18 | 6, 3 => 19 | 6, 4 => 12
      | 6, 5 => 9 | 6, 6 => 8 | 6, 7 => 5 | 6, 8 => 4 | 6, 9 => 5
      | 7, 0 => 16 | 7, 1 => 15 | 7, 2 => 14 | 7, 3 => 13 | 7, 4 => 12
      | 7, 5 => 8 | 7, 6 => 7 | 7, 7 => 6 | 7, 8 => 3 | 7, 9 => 2
      | 8, 0 => 15 | 8, 1 => 14 | 8, 2 => 13 | 8, 3 => 12 | 8, 4 => 11
      | 8, 5 => 10 | 8, 6 => 8 | 8, 7 => 9 | 8, 8 => 2 | 8, 9 => 1
      | 9, 0 => 16 | 9, 1 => 15 | 9, 2 => 14 | 9, 3 => 13 | 9, 4 => 12
      | 9, 5 => 11 | 9, 6 => 9 | 9, 7 => 10 | 9, 8 => 3 | 9, 9 => 2
      | _, _ => 0

private inductive FiniteU11PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 11 11)
  | vertical (edge : VerticalGridEdge 11 11)

private def FiniteU11PrimalEdge.primalEndpoints :
    FiniteU11PrimalEdge → GridVertex 11 11 × GridVertex 11 11
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU11PrimalEdge.dualEndpoints :
    FiniteU11PrimalEdge → GridFace 11 11 × GridFace 11 11
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU11ParentEdge : GridFace 11 11 → FiniteU11PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .vertical ⟨0, 1⟩
      | 0, 1 => .horizontal ⟨1, 1⟩ | 0, 2 => .horizontal ⟨1, 2⟩
      | 0, 3 => .horizontal ⟨1, 3⟩ | 0, 4 => .horizontal ⟨1, 4⟩
      | 0, 5 => .horizontal ⟨1, 5⟩ | 0, 6 => .horizontal ⟨1, 6⟩
      | 0, 7 => .horizontal ⟨1, 7⟩ | 0, 8 => .horizontal ⟨1, 8⟩
      | 0, 9 => .horizontal ⟨1, 9⟩
      | 1, 0 => .vertical ⟨1, 1⟩ | 1, 1 => .horizontal ⟨2, 1⟩
      | 1, 2 => .vertical ⟨1, 2⟩ | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .horizontal ⟨2, 4⟩ | 1, 5 => .vertical ⟨1, 5⟩
      | 1, 6 => .vertical ⟨1, 6⟩ | 1, 7 => .vertical ⟨1, 7⟩
      | 1, 8 => .vertical ⟨1, 8⟩ | 1, 9 => .vertical ⟨1, 9⟩
      | 2, 0 => .vertical ⟨2, 1⟩ | 2, 1 => .vertical ⟨2, 2⟩
      | 2, 2 => .horizontal ⟨3, 2⟩ | 2, 3 => .horizontal ⟨3, 3⟩
      | 2, 4 => .vertical ⟨2, 4⟩ | 2, 5 => .horizontal ⟨2, 5⟩
      | 2, 6 => .horizontal ⟨2, 6⟩ | 2, 7 => .horizontal ⟨2, 7⟩
      | 2, 8 => .horizontal ⟨2, 8⟩ | 2, 9 => .vertical ⟨2, 9⟩
      | 3, 0 => .vertical ⟨3, 1⟩ | 3, 1 => .horizontal ⟨3, 1⟩
      | 3, 2 => .vertical ⟨3, 3⟩ | 3, 3 => .vertical ⟨3, 4⟩
      | 3, 4 => .horizontal ⟨4, 4⟩ | 3, 5 => .horizontal ⟨4, 5⟩
      | 3, 6 => .horizontal ⟨4, 6⟩ | 3, 7 => .horizontal ⟨4, 7⟩
      | 3, 8 => .horizontal ⟨4, 8⟩ | 3, 9 => .vertical ⟨3, 9⟩
      | 4, 0 => .vertical ⟨4, 1⟩ | 4, 1 => .horizontal ⟨5, 1⟩
      | 4, 2 => .vertical ⟨4, 3⟩ | 4, 3 => .horizontal ⟨4, 3⟩
      | 4, 4 => .vertical ⟨4, 5⟩ | 4, 5 => .horizontal ⟨5, 5⟩
      | 4, 6 => .vertical ⟨4, 6⟩ | 4, 7 => .vertical ⟨4, 8⟩
      | 4, 8 => .horizontal ⟨5, 8⟩ | 4, 9 => .vertical ⟨4, 9⟩
      | 5, 0 => .vertical ⟨5, 1⟩ | 5, 1 => .vertical ⟨5, 2⟩
      | 5, 2 => .horizontal ⟨5, 2⟩ | 5, 3 => .vertical ⟨5, 3⟩
      | 5, 4 => .vertical ⟨5, 5⟩ | 5, 5 => .horizontal ⟨6, 5⟩
      | 5, 6 => .vertical ⟨5, 6⟩ | 5, 7 => .vertical ⟨5, 8⟩
      | 5, 8 => .horizontal ⟨6, 8⟩ | 5, 9 => .vertical ⟨5, 9⟩
      | 6, 0 => .vertical ⟨6, 1⟩ | 6, 1 => .horizontal ⟨6, 1⟩
      | 6, 2 => .horizontal ⟨6, 2⟩ | 6, 3 => .horizontal ⟨6, 3⟩
      | 6, 4 => .horizontal ⟨6, 4⟩ | 6, 5 => .vertical ⟨6, 6⟩
      | 6, 6 => .horizontal ⟨7, 6⟩ | 6, 7 => .vertical ⟨6, 8⟩
      | 6, 8 => .horizontal ⟨7, 8⟩ | 6, 9 => .vertical ⟨6, 9⟩
      | 7, 0 => .vertical ⟨7, 1⟩ | 7, 1 => .horizontal ⟨8, 1⟩
      | 7, 2 => .horizontal ⟨8, 2⟩ | 7, 3 => .horizontal ⟨8, 3⟩
      | 7, 4 => .horizontal ⟨8, 4⟩ | 7, 5 => .vertical ⟨7, 6⟩
      | 7, 6 => .vertical ⟨7, 7⟩ | 7, 7 => .horizontal ⟨7, 7⟩
      | 7, 8 => .vertical ⟨7, 9⟩ | 7, 9 => .horizontal ⟨8, 9⟩
      | 8, 0 => .vertical ⟨8, 1⟩ | 8, 1 => .vertical ⟨8, 2⟩
      | 8, 2 => .vertical ⟨8, 3⟩ | 8, 3 => .vertical ⟨8, 4⟩
      | 8, 4 => .vertical ⟨8, 5⟩ | 8, 5 => .vertical ⟨8, 6⟩
      | 8, 6 => .horizontal ⟨8, 6⟩ | 8, 7 => .vertical ⟨8, 7⟩
      | 8, 8 => .vertical ⟨8, 9⟩ | 8, 9 => .vertical ⟨8, 10⟩
      | 9, 0 => .vertical ⟨9, 1⟩ | 9, 1 => .horizontal ⟨9, 1⟩
      | 9, 2 => .horizontal ⟨9, 2⟩ | 9, 3 => .horizontal ⟨9, 3⟩
      | 9, 4 => .horizontal ⟨9, 4⟩ | 9, 5 => .horizontal ⟨9, 5⟩
      | 9, 6 => .horizontal ⟨9, 6⟩ | 9, 7 => .horizontal ⟨9, 7⟩
      | 9, 8 => .horizontal ⟨9, 8⟩ | 9, 9 => .horizontal ⟨9, 9⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU11PrimalEdge_adj (e : FiniteU11PrimalEdge)
    (x y : GridFace 11 11) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU11)
    (h₂ : e.primalEndpoints.2 ∈ finiteU11)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU11).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU11_parent_ne (f : GridFace 11 11) (hf : f ≠ .out) :
    f ≠ finiteU11Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

set_option maxHeartbeats 4000000 in
private theorem finiteU11_parent_edge_data (f : GridFace 11 11) (hf : f ≠ .out) :
    let e := finiteU11ParentEdge f
    e.primalEndpoints.1 ∈ finiteU11 ∧
      e.primalEndpoints.2 ∈ finiteU11 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU11Parent f) := by
  simp only [finiteU11, Finset.mem_filter, Finset.mem_univ, true_and, HasDualEndpoints]
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> decide

/-- The explicit ranked parent certificate on all one hundred and one faces. -/
def finiteU11RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU11) where
  root := .out
  parent := finiteU11Parent
  rank := finiteU11Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU11_parent_edge_data f hf
    exact finiteU11PrimalEdge_adj (finiteU11ParentEdge f) f (finiteU11Parent f)
      (finiteU11_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;> decide

theorem finiteU11_compl_card :
    ((Finset.univ : Finset (GridVertex 11 11)) \ finiteU11).card = 49 := by
  have hU : finiteU11.card = 72 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 121 - 72 = 49
  norm_num

/-- Forty-nine vertices can be preserved in the eleven-by-eleven grid. -/
theorem fortyNine_le_maxPreserved_eleven_eleven : 49 ≤ maxPreserved 11 11 := by
  rw [← finiteU11_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU11 finiteU11RankedDualCertificate

end GridGraphs
