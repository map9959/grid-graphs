import GridGraphs.ConstructionCertificate

/-!
# The finite diagonal construction for eight rows

This file records the row-mask construction `[0, 255, 118, 94, 122, 110,
254, 130]`.  Connectivity of its U-U dual is certified by an explicit parent
edge and rank for each of the forty-nine bounded faces.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The mask in row `r` of the eight-by-eight construction. -/
def finiteU8Mask : Nat → Nat
  | 0 => 0
  | 1 => 255
  | 2 => 118
  | 3 => 94
  | 4 => 122
  | 5 => 110
  | 6 => 254
  | 7 => 130
  | _ => 0

/-- Boolean membership in the row-mask construction. -/
private def finiteU8Selected (v : GridVertex 8 8) : Bool :=
    match v.1.val with
    | 0 => false
    | 1 => true
    | 2 => v.2.val == 1 || v.2.val == 2 || v.2.val == 4 ||
        v.2.val == 5 || v.2.val == 6
    | 3 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
        v.2.val == 4 || v.2.val == 6
    | 4 => v.2.val == 1 || v.2.val == 3 || v.2.val == 4 ||
        v.2.val == 5 || v.2.val == 6
    | 5 => v.2.val == 1 || v.2.val == 2 || v.2.val == 3 ||
        v.2.val == 5 || v.2.val == 6
    | 6 => 1 ≤ v.2.val
    | 7 => v.2.val == 1 || v.2.val == 7
    | _ => false

/-- The selected vertices with row masks
`[0, 255, 118, 94, 122, 110, 254, 130]`. -/
def finiteU8 : Finset (GridVertex 8 8) :=
  Finset.univ.filter fun v => finiteU8Selected v = true

/-- The explicit parent of every dual face. -/
def finiteU8Parent : GridFace 8 8 → GridFace 8 8
  | .out => .out
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .cell 1 0
      | 0, 1 => .cell 1 1
      | 0, 2 => .cell 1 2
      | 0, 3 => .cell 1 3
      | 0, 4 => .cell 1 4
      | 0, 5 => .cell 1 5
      | 0, 6 => .cell 1 6
      | 1, 0 => .cell 1 1
      | 1, 1 => .cell 2 1
      | 1, 2 => .cell 1 1
      | 1, 3 => .cell 1 4
      | 1, 4 => .cell 2 4
      | 1, 5 => .cell 1 4
      | 1, 6 => .cell 1 5
      | 2, 0 => .cell 2 1
      | 2, 1 => .cell 2 2
      | 2, 2 => .cell 3 2
      | 2, 3 => .cell 3 3
      | 2, 4 => .cell 2 3
      | 2, 5 => .cell 1 5
      | 2, 6 => .cell 2 5
      | 3, 0 => .cell 3 1
      | 3, 1 => .cell 2 1
      | 3, 2 => .cell 3 3
      | 3, 3 => .cell 3 4
      | 3, 4 => .cell 4 4
      | 3, 5 => .cell 4 5
      | 3, 6 => .cell 3 5
      | 4, 0 => .cell 4 1
      | 4, 1 => .cell 5 1
      | 4, 2 => .cell 4 3
      | 4, 3 => .cell 3 3
      | 4, 4 => .cell 4 5
      | 4, 5 => .cell 5 5
      | 4, 6 => .cell 4 5
      | 5, 0 => .cell 5 1
      | 5, 1 => .cell 5 2
      | 5, 2 => .cell 4 2
      | 5, 3 => .cell 5 2
      | 5, 4 => .cell 5 5
      | 5, 5 => .cell 5 6
      | 5, 6 => .cell 6 6
      | 6, 0 => .cell 6 1
      | 6, 1 => .cell 5 1
      | 6, 2 => .cell 5 2
      | 6, 3 => .cell 5 3
      | 6, 4 => .cell 5 4
      | 6, 5 => .cell 5 5
      | 6, 6 => .out
      | _, _ => .out

/-- Depths in `finiteU8Parent`, with the outside face at rank zero. -/
def finiteU8Rank : GridFace 8 8 → Nat
  | .out => 0
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => 13 | 0, 1 => 12 | 0, 2 => 13 | 0, 3 => 12
      | 0, 4 => 11 | 0, 5 => 12 | 0, 6 => 13
      | 1, 0 => 12 | 1, 1 => 11 | 1, 2 => 12 | 1, 3 => 11
      | 1, 4 => 10 | 1, 5 => 11 | 1, 6 => 12
      | 2, 0 => 11 | 2, 1 => 10 | 2, 2 => 9 | 2, 3 => 8
      | 2, 4 => 9 | 2, 5 => 12 | 2, 6 => 13
      | 3, 0 => 12 | 3, 1 => 11 | 3, 2 => 8 | 3, 3 => 7
      | 3, 4 => 6 | 3, 5 => 5 | 3, 6 => 6
      | 4, 0 => 13 | 4, 1 => 12 | 4, 2 => 9 | 4, 3 => 8
      | 4, 4 => 5 | 4, 5 => 4 | 4, 6 => 5
      | 5, 0 => 12 | 5, 1 => 11 | 5, 2 => 10 | 5, 3 => 11
      | 5, 4 => 4 | 5, 5 => 3 | 5, 6 => 2
      | 6, 0 => 13 | 6, 1 => 12 | 6, 2 => 11 | 6, 3 => 12
      | 6, 4 => 5 | 6, 5 => 4 | 6, 6 => 1
      | _, _ => 0

private inductive FiniteU8PrimalEdge where
  | horizontal (edge : HorizontalGridEdge 8 8)
  | vertical (edge : VerticalGridEdge 8 8)

private def FiniteU8PrimalEdge.primalEndpoints :
    FiniteU8PrimalEdge → GridVertex 8 8 × GridVertex 8 8
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

private def FiniteU8PrimalEdge.dualEndpoints :
    FiniteU8PrimalEdge → GridFace 8 8 × GridFace 8 8
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The concrete U-U primal edge crossed by each parent edge. -/
private def finiteU8ParentEdge : GridFace 8 8 → FiniteU8PrimalEdge
  | .out => .horizontal ⟨0, 0⟩
  | .cell r c =>
      match r.val, c.val with
      | 0, 0 => .horizontal ⟨1, 0⟩
      | 0, 1 => .horizontal ⟨1, 1⟩
      | 0, 2 => .horizontal ⟨1, 2⟩
      | 0, 3 => .horizontal ⟨1, 3⟩
      | 0, 4 => .horizontal ⟨1, 4⟩
      | 0, 5 => .horizontal ⟨1, 5⟩
      | 0, 6 => .horizontal ⟨1, 6⟩
      | 1, 0 => .vertical ⟨1, 1⟩
      | 1, 1 => .horizontal ⟨2, 1⟩
      | 1, 2 => .vertical ⟨1, 2⟩
      | 1, 3 => .vertical ⟨1, 4⟩
      | 1, 4 => .horizontal ⟨2, 4⟩
      | 1, 5 => .vertical ⟨1, 5⟩
      | 1, 6 => .vertical ⟨1, 6⟩
      | 2, 0 => .vertical ⟨2, 1⟩
      | 2, 1 => .vertical ⟨2, 2⟩
      | 2, 2 => .horizontal ⟨3, 2⟩
      | 2, 3 => .horizontal ⟨3, 3⟩
      | 2, 4 => .vertical ⟨2, 4⟩
      | 2, 5 => .horizontal ⟨2, 5⟩
      | 2, 6 => .vertical ⟨2, 6⟩
      | 3, 0 => .vertical ⟨3, 1⟩
      | 3, 1 => .horizontal ⟨3, 1⟩
      | 3, 2 => .vertical ⟨3, 3⟩
      | 3, 3 => .vertical ⟨3, 4⟩
      | 3, 4 => .horizontal ⟨4, 4⟩
      | 3, 5 => .horizontal ⟨4, 5⟩
      | 3, 6 => .vertical ⟨3, 6⟩
      | 4, 0 => .vertical ⟨4, 1⟩
      | 4, 1 => .horizontal ⟨5, 1⟩
      | 4, 2 => .vertical ⟨4, 3⟩
      | 4, 3 => .horizontal ⟨4, 3⟩
      | 4, 4 => .vertical ⟨4, 5⟩
      | 4, 5 => .horizontal ⟨5, 5⟩
      | 4, 6 => .vertical ⟨4, 6⟩
      | 5, 0 => .vertical ⟨5, 1⟩
      | 5, 1 => .vertical ⟨5, 2⟩
      | 5, 2 => .horizontal ⟨5, 2⟩
      | 5, 3 => .vertical ⟨5, 3⟩
      | 5, 4 => .vertical ⟨5, 5⟩
      | 5, 5 => .vertical ⟨5, 6⟩
      | 5, 6 => .horizontal ⟨6, 6⟩
      | 6, 0 => .vertical ⟨6, 1⟩
      | 6, 1 => .horizontal ⟨6, 1⟩
      | 6, 2 => .horizontal ⟨6, 2⟩
      | 6, 3 => .horizontal ⟨6, 3⟩
      | 6, 4 => .horizontal ⟨6, 4⟩
      | 6, 5 => .horizontal ⟨6, 5⟩
      | 6, 6 => .vertical ⟨6, 7⟩
      | _, _ => .horizontal ⟨0, 0⟩

private theorem finiteU8PrimalEdge_adj (e : FiniteU8PrimalEdge)
    (x y : GridFace 8 8) (hne : x ≠ y)
    (h₁ : e.primalEndpoints.1 ∈ finiteU8)
    (h₂ : e.primalEndpoints.2 ∈ finiteU8)
    (hdual : HasDualEndpoints e.dualEndpoints x y) :
    (uuDualGraph finiteU8).Adj x y := by
  cases e with
  | horizontal e => exact ⟨hne, Or.inl ⟨e, h₁, h₂, hdual⟩⟩
  | vertical e => exact ⟨hne, Or.inr ⟨e, h₁, h₂, hdual⟩⟩

private theorem finiteU8_parent_ne (f : GridFace 8 8) (hf : f ≠ .out) :
    f ≠ finiteU8Parent f := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;> simp [finiteU8Parent]

set_option maxHeartbeats 2000000 in
private theorem finiteU8_parent_edge_data (f : GridFace 8 8) (hf : f ≠ .out) :
    let e := finiteU8ParentEdge f
    e.primalEndpoints.1 ∈ finiteU8 ∧
      e.primalEndpoints.2 ∈ finiteU8 ∧
      HasDualEndpoints e.dualEndpoints f (finiteU8Parent f) := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c <;>
        norm_num [finiteU8ParentEdge, FiniteU8PrimalEdge.primalEndpoints,
          FiniteU8PrimalEdge.dualEndpoints, finiteU8, finiteU8Mask,
          finiteU8Selected,
          finiteU8Parent, horizontalPrimalEndpoints, verticalPrimalEndpoints,
          horizontalDualEndpoints, verticalDualEndpoints, HasDualEndpoints,
          Fin.mk.injEq] <;> simp

/-- The explicit ranked parent certificate on all fifty dual faces. -/
def finiteU8RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU8) where
  root := .out
  parent := finiteU8Parent
  rank := finiteU8Rank
  parent_adj := by
    intro f hf
    obtain ⟨h₁, h₂, hdual⟩ := finiteU8_parent_edge_data f hf
    exact finiteU8PrimalEdge_adj (finiteU8ParentEdge f) f (finiteU8Parent f)
      (finiteU8_parent_ne f hf) h₁ h₂ hdual
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU8Parent, finiteU8Rank]

theorem finiteU8_compl_card :
    ((Finset.univ : Finset (GridVertex 8 8)) \ finiteU8).card = 27 := by
  have hU : finiteU8.card = 37 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 64 - 37 = 27
  norm_num

/-- Twenty-seven vertices can be preserved in the eight-by-eight grid. -/
theorem twentySeven_le_maxPreserved_eight_eight : 27 ≤ maxPreserved 8 8 := by
  rw [← finiteU8_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU8 finiteU8RankedDualCertificate

end GridGraphs
