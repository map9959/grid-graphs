import GridGraphs.GridEdge
import GridGraphs.PrimalContourLedger

/-!
# Bare comb transitions

This file isolates the four orientations of the bare-comb argument.  Leaves run
along a row or column, their retained tree edges point into a cotree-free
carrier, and the unit cells considered here lie on the opposite side.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

/-- Coordinate-labelled edges omitted by `T`. -/
def LabelledCotreeTransition {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  {e : GridEdge m n // e.primalSym2 ∈ (gridGraph m n \ T).edgeFinset}

/-- The coordinate and tree data for a horizontal south-pointing bare comb.
There are `gapCount + 1` leaves and carrier vertices, hence `gapCount`
north-side unit cells. -/
structure HorizontalSouthBareComb {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] where
  spanning : IsSpanningSubtree (gridGraph m n) T
  row : Nat
  startCol : Nat
  gapCount : Nat
  row_pos : 0 < row
  south_row_lt : row + 1 < m
  run_lt : startCol + gapCount < n
  leaf_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n) ∈
      supportFinset (gridGraph m n \ T)
  carrier_not_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨row + 1, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n) ∉
      supportFinset (gridGraph m n \ T)
  leaf_degree : ∀ i : Fin (gapCount + 1),
    T.degree ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) :
      GridVertex m n) = 1
  south_retained : ∀ i : Fin (gapCount + 1),
    T.Adj
      ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n)
      ((⟨row + 1, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n)

namespace HorizontalSouthBareComb

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (C : HorizontalSouthBareComb T)

def runIndex (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row, by have := C.south_row_lt; omega⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def carrier (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row + 1, C.south_row_lt⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def outer (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row - 1, by have := C.south_row_lt; omega⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def gapLeft (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val, by omega⟩

def gapRight (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The fourth (north/top) edge of the outward unit cell at a gap. -/
def fourthEdge (i : Fin C.gapCount) : GridEdge m n :=
  .horizontal
    { row := ⟨C.row - 1, by have := C.south_row_lt; omega⟩
      col := ⟨C.startCol + i.val, by
        have := C.run_lt
        have := i.isLt
        omega⟩ }

@[simp] theorem fourthEdge_primalSym2 (i : Fin C.gapCount) :
    (C.fourthEdge i).primalSym2 =
      s(C.outer (C.gapLeft i), C.outer (C.gapRight i)) := by
  simp [fourthEdge, GridEdge.primalSym2, horizontalPrimalEndpoints, outer,
    gapLeft, gapRight, Nat.add_assoc]

private theorem grid_adj_run_carrier (i : Fin (C.gapCount + 1)) :
    (gridGraph m n).Adj (C.runIndex i) (C.carrier i) := by
  change adjacent m n _ _
  right
  exact ⟨rfl, Or.inl (by simp [runIndex, carrier])⟩

private theorem grid_adj_run_outer (i : Fin (C.gapCount + 1)) :
    (gridGraph m n).Adj (C.runIndex i) (C.outer i) := by
  change adjacent m n _ _
  right
  refine ⟨rfl, Or.inr ?_⟩
  simp [runIndex, outer]
  have := C.row_pos
  omega

private theorem grid_adj_gap_runs (i : Fin C.gapCount) :
    (gridGraph m n).Adj (C.runIndex (C.gapLeft i))
      (C.runIndex (C.gapRight i)) := by
  change adjacent m n _ _
  left
  exact ⟨rfl, Or.inl (by simp [runIndex, gapLeft, gapRight, Nat.add_assoc])⟩

private theorem grid_adj_gap_outers (i : Fin C.gapCount) :
    (gridGraph m n).Adj (C.outer (C.gapLeft i))
      (C.outer (C.gapRight i)) := by
  change adjacent m n _ _
  left
  exact ⟨rfl, Or.inl (by simp [outer, gapLeft, gapRight, Nat.add_assoc])⟩

private theorem not_adj_of_leaf {v root w : GridVertex m n}
    (hdegree : T.degree v = 1) (hroot : T.Adj v root) (hne : w ≠ root) :
    ¬T.Adj v w := by
  intro hw
  have hsubset : {root, w} ⊆ T.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      simpa using hroot
    · subst x
      simpa using hw
  have hcard := Finset.card_le_card hsubset
  have hrootw : root ≠ w := fun h => hne h.symm
  change (T.neighborFinset v).card = 1 at hdegree
  rw [hdegree] at hcard
  simp [hrootw] at hcard

/-- The leaf-to-leaf side of every outward unit cell is omitted. -/
theorem not_adj_gap_runs (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.runIndex (C.gapRight i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapLeft i))
    (C.south_retained (C.gapLeft i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [runIndex] at hrow

/-- The left north-pointing side of every outward unit cell is omitted. -/
theorem not_adj_left_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.outer (C.gapLeft i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapLeft i))
    (C.south_retained (C.gapLeft i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [outer] at hrow

/-- The right north-pointing side of every outward unit cell is omitted. -/
theorem not_adj_right_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapRight i)) (C.outer (C.gapRight i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapRight i))
    (C.south_retained (C.gapRight i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [outer] at hrow

/-- The three non-fourth sides of the outward unit cell are all omitted. -/
theorem outward_cell_other_edges_omitted (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.runIndex (C.gapRight i)) ∧
      ¬T.Adj (C.runIndex (C.gapLeft i)) (C.outer (C.gapLeft i)) ∧
      ¬T.Adj (C.runIndex (C.gapRight i)) (C.outer (C.gapRight i)) :=
  ⟨C.not_adj_gap_runs i, C.not_adj_left_outer i, C.not_adj_right_outer i⟩

/-- Both outer vertices of a gap belong to cotree support. -/
theorem outer_mem_cotree_support (i : Fin C.gapCount) :
    C.outer (C.gapLeft i) ∈ supportFinset (gridGraph m n \ T) ∧
      C.outer (C.gapRight i) ∈ supportFinset (gridGraph m n \ T) := by
  constructor
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapLeft i),
      ⟨(C.grid_adj_run_outer (C.gapLeft i)).symm,
        fun h => C.not_adj_left_outer i h.symm⟩⟩
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapRight i),
      ⟨(C.grid_adj_run_outer (C.gapRight i)).symm,
        fun h => C.not_adj_right_outer i h.symm⟩⟩

/-- The fourth edge is an internal supported tree edge exactly in the retained
case; otherwise its coordinate label is a cotree transition. -/
theorem fourthEdge_dichotomy (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      (C.fourthEdge i).primalSym2 ∈
        internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ∨
    (¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      (C.fourthEdge i).primalSym2 ∈ (gridGraph m n \ T).edgeFinset) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · left
    refine ⟨h, (mem_internalEdgeFinset _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
      exact h
    · intro v hv
      rw [C.fourthEdge_primalSym2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (C.outer_mem_cotree_support i).1
      · exact (C.outer_mem_cotree_support i).2
  · right
    refine ⟨h, ?_⟩
    rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
    exact ⟨C.grid_adj_gap_outers i, h⟩

/-- Subtype-packaged form of `fourthEdge_dichotomy`, retaining the coordinate
`GridEdge` label in the cotree case. -/
theorem fourthEdge_internal_or_labelledCotree (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      ∃ e : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))),
        e.1 = (C.fourthEdge i).primalSym2) ∨
    (¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      ∃ e : LabelledCotreeTransition T, e.1 = C.fourthEdge i) := by
  classical
  rcases C.fourthEdge_dichotomy i with h | h
  · exact Or.inl ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩
  · exact Or.inr ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩

/-- Distinct gaps have distinct fourth-edge labels. -/
theorem fourthEdge_injective : Function.Injective C.fourthEdge := by
  intro i j h
  have h' : C.startCol + i.val = C.startCol + j.val := by
    have := congrArg (fun e : GridEdge m n => match e with
      | .horizontal a => a.col.val
      | .vertical _ => 0) h
    simpa [fourthEdge] using this
  exact Fin.ext (by omega)

/-- Gap resources, classified into retained internal edges and labelled cotree
transitions. -/
noncomputable def gapResourceEmbedding :
    Fin C.gapCount ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        LabelledCotreeTransition T) where
  toFun i := by
    classical
    if h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) then
      exact Sum.inl ⟨(C.fourthEdge i).primalSym2,
        (C.fourthEdge_dichotomy i).resolve_right (fun hn => hn.1 h) |>.2⟩
    else
      exact Sum.inr ⟨C.fourthEdge i,
        (C.fourthEdge_dichotomy i).resolve_left (fun ht => h ht.1) |>.2⟩
  inj' := by
    classical
    intro i j hij
    by_cases hi : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
    · by_cases hj : T.Adj (C.outer (C.gapLeft j)) (C.outer (C.gapRight j))
      · simp [hi, hj] at hij
        rcases hij with hij | hij
        · apply Fin.ext
          have hcol := congrArg (fun v : GridVertex m n => v.2.val) hij.1
          simp [outer, gapLeft] at hcol
          omega
        · have hcol := congrArg (fun v : GridVertex m n => v.2.val) hij.1
          have hcol' := congrArg (fun v : GridVertex m n => v.2.val) hij.2
          simp [outer, gapLeft, gapRight] at hcol hcol'
          omega
      · simp [hi, hj] at hij
    · by_cases hj : T.Adj (C.outer (C.gapLeft j)) (C.outer (C.gapRight j))
      · simp [hi, hj] at hij
      · simp [hi, hj] at hij
        exact C.fourthEdge_injective (congrArg Subtype.val hij)

theorem gapResourceEmbedding_isLeft_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inl e) ↔
      T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

theorem gapResourceEmbedding_isRight_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inr e) ↔
      ¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

end HorizontalSouthBareComb

/-- The coordinate and tree data for the opposite horizontal bare-comb
orientation.  Leaves lie south of the carrier, their retained tree edges point
north, and the outward unit cells lie south of the leaves. -/
structure HorizontalNorthBareComb {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] where
  spanning : IsSpanningSubtree (gridGraph m n) T
  row : Nat
  startCol : Nat
  gapCount : Nat
  row_pos : 0 < row
  outer_row_lt : row + 1 < m
  run_lt : startCol + gapCount < n
  leaf_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n) ∈
      supportFinset (gridGraph m n \ T)
  carrier_not_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨row - 1, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n) ∉
      supportFinset (gridGraph m n \ T)
  leaf_degree : ∀ i : Fin (gapCount + 1),
    T.degree ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) :
      GridVertex m n) = 1
  north_retained : ∀ i : Fin (gapCount + 1),
    T.Adj
      ((⟨row, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n)
      ((⟨row - 1, by omega⟩, ⟨startCol + i.val, by omega⟩) : GridVertex m n)

namespace HorizontalNorthBareComb

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (C : HorizontalNorthBareComb T)

def runIndex (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row, by have := C.outer_row_lt; omega⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def carrier (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row - 1, by have := C.outer_row_lt; omega⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def outer (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.row + 1, C.outer_row_lt⟩,
    ⟨C.startCol + i.val, by have := C.run_lt; have := i.isLt; omega⟩)

def gapLeft (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val, by omega⟩

def gapRight (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The fourth (south/bottom) edge of the outward unit cell at a gap. -/
def fourthEdge (i : Fin C.gapCount) : GridEdge m n :=
  .horizontal
    { row := ⟨C.row + 1, C.outer_row_lt⟩
      col := ⟨C.startCol + i.val, by
        have := C.run_lt
        have := i.isLt
        omega⟩ }

@[simp] theorem fourthEdge_primalSym2 (i : Fin C.gapCount) :
    (C.fourthEdge i).primalSym2 =
      s(C.outer (C.gapLeft i), C.outer (C.gapRight i)) := by
  simp [fourthEdge, GridEdge.primalSym2, horizontalPrimalEndpoints, outer,
    gapLeft, gapRight, Nat.add_assoc]

private theorem grid_adj_run_outer (i : Fin (C.gapCount + 1)) :
    (gridGraph m n).Adj (C.runIndex i) (C.outer i) := by
  change adjacent m n _ _
  right
  exact ⟨rfl, Or.inl (by simp [runIndex, outer])⟩

private theorem grid_adj_gap_outers (i : Fin C.gapCount) :
    (gridGraph m n).Adj (C.outer (C.gapLeft i))
      (C.outer (C.gapRight i)) := by
  change adjacent m n _ _
  left
  exact ⟨rfl, Or.inl (by simp [outer, gapLeft, gapRight, Nat.add_assoc])⟩

private theorem not_adj_of_leaf {v root w : GridVertex m n}
    (hdegree : T.degree v = 1) (hroot : T.Adj v root) (hne : w ≠ root) :
    ¬T.Adj v w := by
  intro hw
  have hsubset : {root, w} ⊆ T.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa using hroot
    · simpa using hw
  have hcard := Finset.card_le_card hsubset
  have hrootw : root ≠ w := fun h => hne h.symm
  change (T.neighborFinset v).card = 1 at hdegree
  rw [hdegree] at hcard
  simp [hrootw] at hcard

/-- The leaf-to-leaf side of every outward unit cell is omitted. -/
theorem not_adj_gap_runs (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.runIndex (C.gapRight i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapLeft i))
    (C.north_retained (C.gapLeft i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [runIndex] at hrow
  have := C.row_pos
  omega

/-- The left south-pointing side of every outward unit cell is omitted. -/
theorem not_adj_left_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.outer (C.gapLeft i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapLeft i))
    (C.north_retained (C.gapLeft i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [outer] at hrow
  have := C.row_pos
  omega

/-- The right south-pointing side of every outward unit cell is omitted. -/
theorem not_adj_right_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapRight i)) (C.outer (C.gapRight i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapRight i))
    (C.north_retained (C.gapRight i))
  intro h
  have hrow := congrArg (fun v : GridVertex m n => v.1.val) h
  simp [outer] at hrow
  have := C.row_pos
  omega

/-- The three non-fourth sides of the outward unit cell are all omitted. -/
theorem outward_cell_other_edges_omitted (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapLeft i)) (C.runIndex (C.gapRight i)) ∧
      ¬T.Adj (C.runIndex (C.gapLeft i)) (C.outer (C.gapLeft i)) ∧
      ¬T.Adj (C.runIndex (C.gapRight i)) (C.outer (C.gapRight i)) :=
  ⟨C.not_adj_gap_runs i, C.not_adj_left_outer i, C.not_adj_right_outer i⟩

/-- Both outer vertices of a gap belong to cotree support. -/
theorem outer_mem_cotree_support (i : Fin C.gapCount) :
    C.outer (C.gapLeft i) ∈ supportFinset (gridGraph m n \ T) ∧
      C.outer (C.gapRight i) ∈ supportFinset (gridGraph m n \ T) := by
  constructor
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapLeft i),
      ⟨(C.grid_adj_run_outer (C.gapLeft i)).symm,
        fun h => C.not_adj_left_outer i h.symm⟩⟩
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapRight i),
      ⟨(C.grid_adj_run_outer (C.gapRight i)).symm,
        fun h => C.not_adj_right_outer i h.symm⟩⟩

/-- The fourth edge is an internal supported tree edge exactly in the retained
case; otherwise its coordinate label is a cotree transition. -/
theorem fourthEdge_dichotomy (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      (C.fourthEdge i).primalSym2 ∈
        internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ∨
    (¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      (C.fourthEdge i).primalSym2 ∈ (gridGraph m n \ T).edgeFinset) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · left
    refine ⟨h, (mem_internalEdgeFinset _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
      exact h
    · intro v hv
      rw [C.fourthEdge_primalSym2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (C.outer_mem_cotree_support i).1
      · exact (C.outer_mem_cotree_support i).2
  · right
    refine ⟨h, ?_⟩
    rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
    exact ⟨C.grid_adj_gap_outers i, h⟩

/-- Subtype-packaged form of `fourthEdge_dichotomy`, retaining the coordinate
`GridEdge` label in the cotree case. -/
theorem fourthEdge_internal_or_labelledCotree (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      ∃ e : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))),
        e.1 = (C.fourthEdge i).primalSym2) ∨
    (¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) ∧
      ∃ e : LabelledCotreeTransition T, e.1 = C.fourthEdge i) := by
  classical
  rcases C.fourthEdge_dichotomy i with h | h
  · exact Or.inl ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩
  · exact Or.inr ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩

/-- Distinct gaps have distinct fourth-edge labels. -/
theorem fourthEdge_injective : Function.Injective C.fourthEdge := by
  intro i j h
  have h' : C.startCol + i.val = C.startCol + j.val := by
    have := congrArg (fun e : GridEdge m n => match e with
      | .horizontal a => a.col.val
      | .vertical _ => 0) h
    simpa [fourthEdge] using this
  exact Fin.ext (by omega)

/-- Gap resources, classified into retained internal edges and labelled cotree
transitions. -/
noncomputable def gapResourceEmbedding :
    Fin C.gapCount ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        LabelledCotreeTransition T) where
  toFun i := by
    classical
    if h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) then
      exact Sum.inl ⟨(C.fourthEdge i).primalSym2,
        (C.fourthEdge_dichotomy i).resolve_right (fun hn => hn.1 h) |>.2⟩
    else
      exact Sum.inr ⟨C.fourthEdge i,
        (C.fourthEdge_dichotomy i).resolve_left (fun ht => h ht.1) |>.2⟩
  inj' := by
    classical
    intro i j hij
    by_cases hi : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
    · by_cases hj : T.Adj (C.outer (C.gapLeft j)) (C.outer (C.gapRight j))
      · simp [hi, hj] at hij
        rcases hij with hij | hij
        · apply Fin.ext
          have hcol := congrArg (fun v : GridVertex m n => v.2.val) hij.1
          simp [outer, gapLeft] at hcol
          omega
        · have hcol := congrArg (fun v : GridVertex m n => v.2.val) hij.1
          have hcol' := congrArg (fun v : GridVertex m n => v.2.val) hij.2
          simp [outer, gapLeft, gapRight] at hcol hcol'
          omega
      · simp [hi, hj] at hij
    · by_cases hj : T.Adj (C.outer (C.gapLeft j)) (C.outer (C.gapRight j))
      · simp [hi, hj] at hij
      · simp [hi, hj] at hij
        exact C.fourthEdge_injective (congrArg Subtype.val hij)

theorem gapResourceEmbedding_isLeft_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inl e) ↔
      T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

theorem gapResourceEmbedding_isRight_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inr e) ↔
      ¬T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapLeft i)) (C.outer (C.gapRight i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

end HorizontalNorthBareComb

/-- The coordinate and tree data for an east-pointing vertical bare comb.
Leaves run vertically west of the carrier, and the outward unit cells lie west
of the leaves. -/
structure VerticalEastBareComb {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] where
  spanning : IsSpanningSubtree (gridGraph m n) T
  startRow : Nat
  col : Nat
  gapCount : Nat
  col_pos : 0 < col
  east_col_lt : col + 1 < n
  run_lt : startRow + gapCount < m
  leaf_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) : GridVertex m n) ∈
      supportFinset (gridGraph m n \ T)
  carrier_not_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨startRow + i.val, by omega⟩, ⟨col + 1, by omega⟩) : GridVertex m n) ∉
      supportFinset (gridGraph m n \ T)
  leaf_degree : ∀ i : Fin (gapCount + 1),
    T.degree ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) :
      GridVertex m n) = 1
  east_retained : ∀ i : Fin (gapCount + 1),
    T.Adj
      ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) : GridVertex m n)
      ((⟨startRow + i.val, by omega⟩, ⟨col + 1, by omega⟩) : GridVertex m n)

namespace VerticalEastBareComb

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (C : VerticalEastBareComb T)

def runIndex (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col, by have := C.east_col_lt; omega⟩)

def carrier (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col + 1, C.east_col_lt⟩)

def outer (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col - 1, by have := C.east_col_lt; omega⟩)

def gapTop (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val, by omega⟩

def gapBottom (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The fourth (west/left) edge of the outward unit cell at a gap. -/
def fourthEdge (i : Fin C.gapCount) : GridEdge m n :=
  .vertical
    { row := ⟨C.startRow + i.val, by
        have := C.run_lt
        have := i.isLt
        omega⟩
      col := ⟨C.col - 1, by have := C.east_col_lt; omega⟩ }

@[simp] theorem fourthEdge_primalSym2 (i : Fin C.gapCount) :
    (C.fourthEdge i).primalSym2 =
      s(C.outer (C.gapTop i), C.outer (C.gapBottom i)) := by
  simp [fourthEdge, GridEdge.primalSym2, verticalPrimalEndpoints, outer,
    gapTop, gapBottom, Nat.add_assoc]

private theorem grid_adj_run_outer (i : Fin (C.gapCount + 1)) :
    (gridGraph m n).Adj (C.runIndex i) (C.outer i) := by
  change adjacent m n _ _
  left
  refine ⟨rfl, Or.inr ?_⟩
  simp [runIndex, outer]
  have := C.col_pos
  omega

private theorem grid_adj_gap_outers (i : Fin C.gapCount) :
    (gridGraph m n).Adj (C.outer (C.gapTop i))
      (C.outer (C.gapBottom i)) := by
  change adjacent m n _ _
  right
  exact ⟨rfl, Or.inl (by simp [outer, gapTop, gapBottom, Nat.add_assoc])⟩

private theorem not_adj_of_leaf {v root w : GridVertex m n}
    (hdegree : T.degree v = 1) (hroot : T.Adj v root) (hne : w ≠ root) :
    ¬T.Adj v w := by
  intro hw
  have hsubset : {root, w} ⊆ T.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa using hroot
    · simpa using hw
  have hcard := Finset.card_le_card hsubset
  have hrootw : root ≠ w := fun h => hne h.symm
  change (T.neighborFinset v).card = 1 at hdegree
  rw [hdegree] at hcard
  simp [hrootw] at hcard

/-- The leaf-to-leaf side of every outward unit cell is omitted. -/
theorem not_adj_gap_runs (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.runIndex (C.gapBottom i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapTop i))
    (C.east_retained (C.gapTop i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [runIndex] at hcol

/-- The top west-pointing side of every outward unit cell is omitted. -/
theorem not_adj_top_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.outer (C.gapTop i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapTop i))
    (C.east_retained (C.gapTop i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [outer] at hcol

/-- The bottom west-pointing side of every outward unit cell is omitted. -/
theorem not_adj_bottom_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapBottom i)) (C.outer (C.gapBottom i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapBottom i))
    (C.east_retained (C.gapBottom i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [outer] at hcol

/-- The three non-fourth sides of the outward unit cell are all omitted. -/
theorem outward_cell_other_edges_omitted (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.runIndex (C.gapBottom i)) ∧
      ¬T.Adj (C.runIndex (C.gapTop i)) (C.outer (C.gapTop i)) ∧
      ¬T.Adj (C.runIndex (C.gapBottom i)) (C.outer (C.gapBottom i)) :=
  ⟨C.not_adj_gap_runs i, C.not_adj_top_outer i, C.not_adj_bottom_outer i⟩

/-- Both outer vertices of a gap belong to cotree support. -/
theorem outer_mem_cotree_support (i : Fin C.gapCount) :
    C.outer (C.gapTop i) ∈ supportFinset (gridGraph m n \ T) ∧
      C.outer (C.gapBottom i) ∈ supportFinset (gridGraph m n \ T) := by
  constructor
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapTop i),
      ⟨(C.grid_adj_run_outer (C.gapTop i)).symm,
        fun h => C.not_adj_top_outer i h.symm⟩⟩
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapBottom i),
      ⟨(C.grid_adj_run_outer (C.gapBottom i)).symm,
        fun h => C.not_adj_bottom_outer i h.symm⟩⟩

/-- The fourth edge is an internal supported tree edge exactly in the retained
case; otherwise its coordinate label is a cotree transition. -/
theorem fourthEdge_dichotomy (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      (C.fourthEdge i).primalSym2 ∈
        internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ∨
    (¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      (C.fourthEdge i).primalSym2 ∈ (gridGraph m n \ T).edgeFinset) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · left
    refine ⟨h, (mem_internalEdgeFinset _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
      exact h
    · intro v hv
      rw [C.fourthEdge_primalSym2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (C.outer_mem_cotree_support i).1
      · exact (C.outer_mem_cotree_support i).2
  · right
    refine ⟨h, ?_⟩
    rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
    exact ⟨C.grid_adj_gap_outers i, h⟩

/-- Subtype-packaged form of `fourthEdge_dichotomy`, retaining the coordinate
`GridEdge` label in the cotree case. -/
theorem fourthEdge_internal_or_labelledCotree (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      ∃ e : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))),
        e.1 = (C.fourthEdge i).primalSym2) ∨
    (¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      ∃ e : LabelledCotreeTransition T, e.1 = C.fourthEdge i) := by
  classical
  rcases C.fourthEdge_dichotomy i with h | h
  · exact Or.inl ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩
  · exact Or.inr ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩

/-- Distinct gaps have distinct fourth-edge labels. -/
theorem fourthEdge_injective : Function.Injective C.fourthEdge := by
  intro i j h
  have h' : C.startRow + i.val = C.startRow + j.val := by
    have := congrArg (fun e : GridEdge m n => match e with
      | .horizontal _ => 0
      | .vertical a => a.row.val) h
    simpa [fourthEdge] using this
  exact Fin.ext (by omega)

/-- Gap resources, classified into retained internal edges and labelled cotree
transitions. -/
noncomputable def gapResourceEmbedding :
    Fin C.gapCount ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        LabelledCotreeTransition T) where
  toFun i := by
    classical
    if h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) then
      exact Sum.inl ⟨(C.fourthEdge i).primalSym2,
        (C.fourthEdge_dichotomy i).resolve_right (fun hn => hn.1 h) |>.2⟩
    else
      exact Sum.inr ⟨C.fourthEdge i,
        (C.fourthEdge_dichotomy i).resolve_left (fun ht => h ht.1) |>.2⟩
  inj' := by
    classical
    intro i j hij
    by_cases hi : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
    · by_cases hj : T.Adj (C.outer (C.gapTop j)) (C.outer (C.gapBottom j))
      · simp [hi, hj] at hij
        rcases hij with hij | hij
        · apply Fin.ext
          have hrow := congrArg (fun v : GridVertex m n => v.1.val) hij.1
          simp [outer, gapTop] at hrow
          omega
        · have hrow := congrArg (fun v : GridVertex m n => v.1.val) hij.1
          have hrow' := congrArg (fun v : GridVertex m n => v.1.val) hij.2
          simp [outer, gapTop, gapBottom] at hrow hrow'
          omega
      · simp [hi, hj] at hij
    · by_cases hj : T.Adj (C.outer (C.gapTop j)) (C.outer (C.gapBottom j))
      · simp [hi, hj] at hij
      · simp [hi, hj] at hij
        exact C.fourthEdge_injective (congrArg Subtype.val hij)

theorem gapResourceEmbedding_isLeft_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inl e) ↔
      T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

theorem gapResourceEmbedding_isRight_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inr e) ↔
      ¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

end VerticalEastBareComb

/-- The coordinate and tree data for a west-pointing vertical bare comb.
Leaves run vertically east of the carrier, and the outward unit cells lie east
of the leaves. -/
structure VerticalWestBareComb {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] where
  spanning : IsSpanningSubtree (gridGraph m n) T
  startRow : Nat
  col : Nat
  gapCount : Nat
  col_pos : 0 < col
  outer_col_lt : col + 1 < n
  run_lt : startRow + gapCount < m
  leaf_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) : GridVertex m n) ∈
      supportFinset (gridGraph m n \ T)
  carrier_not_mem_support : ∀ i : Fin (gapCount + 1),
    ((⟨startRow + i.val, by omega⟩, ⟨col - 1, by omega⟩) : GridVertex m n) ∉
      supportFinset (gridGraph m n \ T)
  leaf_degree : ∀ i : Fin (gapCount + 1),
    T.degree ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) :
      GridVertex m n) = 1
  west_retained : ∀ i : Fin (gapCount + 1),
    T.Adj
      ((⟨startRow + i.val, by omega⟩, ⟨col, by omega⟩) : GridVertex m n)
      ((⟨startRow + i.val, by omega⟩, ⟨col - 1, by omega⟩) : GridVertex m n)

namespace VerticalWestBareComb

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (C : VerticalWestBareComb T)

def runIndex (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col, by have := C.outer_col_lt; omega⟩)

def carrier (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col - 1, by have := C.outer_col_lt; omega⟩)

def outer (i : Fin (C.gapCount + 1)) : GridVertex m n :=
  (⟨C.startRow + i.val, by have := C.run_lt; have := i.isLt; omega⟩,
    ⟨C.col + 1, C.outer_col_lt⟩)

def gapTop (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val, by omega⟩

def gapBottom (i : Fin C.gapCount) : Fin (C.gapCount + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The fourth (east/right) edge of the outward unit cell at a gap. -/
def fourthEdge (i : Fin C.gapCount) : GridEdge m n :=
  .vertical
    { row := ⟨C.startRow + i.val, by
        have := C.run_lt
        have := i.isLt
        omega⟩
      col := ⟨C.col + 1, C.outer_col_lt⟩ }

@[simp] theorem fourthEdge_primalSym2 (i : Fin C.gapCount) :
    (C.fourthEdge i).primalSym2 =
      s(C.outer (C.gapTop i), C.outer (C.gapBottom i)) := by
  simp [fourthEdge, GridEdge.primalSym2, verticalPrimalEndpoints, outer,
    gapTop, gapBottom, Nat.add_assoc]

private theorem grid_adj_run_outer (i : Fin (C.gapCount + 1)) :
    (gridGraph m n).Adj (C.runIndex i) (C.outer i) := by
  change adjacent m n _ _
  left
  exact ⟨rfl, Or.inl (by simp [runIndex, outer])⟩

private theorem grid_adj_gap_outers (i : Fin C.gapCount) :
    (gridGraph m n).Adj (C.outer (C.gapTop i))
      (C.outer (C.gapBottom i)) := by
  change adjacent m n _ _
  right
  exact ⟨rfl, Or.inl (by simp [outer, gapTop, gapBottom, Nat.add_assoc])⟩

private theorem not_adj_of_leaf {v root w : GridVertex m n}
    (hdegree : T.degree v = 1) (hroot : T.Adj v root) (hne : w ≠ root) :
    ¬T.Adj v w := by
  intro hw
  have hsubset : {root, w} ⊆ T.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa using hroot
    · simpa using hw
  have hcard := Finset.card_le_card hsubset
  have hrootw : root ≠ w := fun h => hne h.symm
  change (T.neighborFinset v).card = 1 at hdegree
  rw [hdegree] at hcard
  simp [hrootw] at hcard

/-- The leaf-to-leaf side of every outward unit cell is omitted. -/
theorem not_adj_gap_runs (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.runIndex (C.gapBottom i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapTop i))
    (C.west_retained (C.gapTop i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [runIndex] at hcol
  have := C.col_pos
  omega

/-- The top east-pointing side of every outward unit cell is omitted. -/
theorem not_adj_top_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.outer (C.gapTop i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapTop i))
    (C.west_retained (C.gapTop i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [outer] at hcol
  have := C.col_pos
  omega

/-- The bottom east-pointing side of every outward unit cell is omitted. -/
theorem not_adj_bottom_outer (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapBottom i)) (C.outer (C.gapBottom i)) := by
  apply not_adj_of_leaf (C.leaf_degree (C.gapBottom i))
    (C.west_retained (C.gapBottom i))
  intro h
  have hcol := congrArg (fun v : GridVertex m n => v.2.val) h
  simp [outer] at hcol
  have := C.col_pos
  omega

/-- The three non-fourth sides of the outward unit cell are all omitted. -/
theorem outward_cell_other_edges_omitted (i : Fin C.gapCount) :
    ¬T.Adj (C.runIndex (C.gapTop i)) (C.runIndex (C.gapBottom i)) ∧
      ¬T.Adj (C.runIndex (C.gapTop i)) (C.outer (C.gapTop i)) ∧
      ¬T.Adj (C.runIndex (C.gapBottom i)) (C.outer (C.gapBottom i)) :=
  ⟨C.not_adj_gap_runs i, C.not_adj_top_outer i, C.not_adj_bottom_outer i⟩

/-- Both outer vertices of a gap belong to cotree support. -/
theorem outer_mem_cotree_support (i : Fin C.gapCount) :
    C.outer (C.gapTop i) ∈ supportFinset (gridGraph m n \ T) ∧
      C.outer (C.gapBottom i) ∈ supportFinset (gridGraph m n \ T) := by
  constructor
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapTop i),
      ⟨(C.grid_adj_run_outer (C.gapTop i)).symm,
        fun h => C.not_adj_top_outer i h.symm⟩⟩
  · rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨C.runIndex (C.gapBottom i),
      ⟨(C.grid_adj_run_outer (C.gapBottom i)).symm,
        fun h => C.not_adj_bottom_outer i h.symm⟩⟩

/-- The fourth edge is an internal supported tree edge exactly in the retained
case; otherwise its coordinate label is a cotree transition. -/
theorem fourthEdge_dichotomy (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      (C.fourthEdge i).primalSym2 ∈
        internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ∨
    (¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      (C.fourthEdge i).primalSym2 ∈ (gridGraph m n \ T).edgeFinset) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · left
    refine ⟨h, (mem_internalEdgeFinset _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
      exact h
    · intro v hv
      rw [C.fourthEdge_primalSym2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (C.outer_mem_cotree_support i).1
      · exact (C.outer_mem_cotree_support i).2
  · right
    refine ⟨h, ?_⟩
    rw [C.fourthEdge_primalSym2, SimpleGraph.mem_edgeFinset]
    exact ⟨C.grid_adj_gap_outers i, h⟩

/-- Subtype-packaged form of `fourthEdge_dichotomy`, retaining the coordinate
`GridEdge` label in the cotree case. -/
theorem fourthEdge_internal_or_labelledCotree (i : Fin C.gapCount) :
    (T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      ∃ e : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))),
        e.1 = (C.fourthEdge i).primalSym2) ∨
    (¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) ∧
      ∃ e : LabelledCotreeTransition T, e.1 = C.fourthEdge i) := by
  classical
  rcases C.fourthEdge_dichotomy i with h | h
  · exact Or.inl ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩
  · exact Or.inr ⟨h.1, ⟨⟨_, h.2⟩, rfl⟩⟩

/-- Distinct gaps have distinct fourth-edge labels. -/
theorem fourthEdge_injective : Function.Injective C.fourthEdge := by
  intro i j h
  have h' : C.startRow + i.val = C.startRow + j.val := by
    have := congrArg (fun e : GridEdge m n => match e with
      | .horizontal _ => 0
      | .vertical a => a.row.val) h
    simpa [fourthEdge] using this
  exact Fin.ext (by omega)

/-- Gap resources, classified into retained internal edges and labelled cotree
transitions. -/
noncomputable def gapResourceEmbedding :
    Fin C.gapCount ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        LabelledCotreeTransition T) where
  toFun i := by
    classical
    if h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) then
      exact Sum.inl ⟨(C.fourthEdge i).primalSym2,
        (C.fourthEdge_dichotomy i).resolve_right (fun hn => hn.1 h) |>.2⟩
    else
      exact Sum.inr ⟨C.fourthEdge i,
        (C.fourthEdge_dichotomy i).resolve_left (fun ht => h ht.1) |>.2⟩
  inj' := by
    classical
    intro i j hij
    by_cases hi : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
    · by_cases hj : T.Adj (C.outer (C.gapTop j)) (C.outer (C.gapBottom j))
      · simp [hi, hj] at hij
        rcases hij with hij | hij
        · apply Fin.ext
          have hrow := congrArg (fun v : GridVertex m n => v.1.val) hij.1
          simp [outer, gapTop] at hrow
          omega
        · have hrow := congrArg (fun v : GridVertex m n => v.1.val) hij.1
          have hrow' := congrArg (fun v : GridVertex m n => v.1.val) hij.2
          simp [outer, gapTop, gapBottom] at hrow hrow'
          omega
      · simp [hi, hj] at hij
    · by_cases hj : T.Adj (C.outer (C.gapTop j)) (C.outer (C.gapBottom j))
      · simp [hi, hj] at hij
      · simp [hi, hj] at hij
        exact C.fourthEdge_injective (congrArg Subtype.val hij)

theorem gapResourceEmbedding_isLeft_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inl e) ↔
      T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

theorem gapResourceEmbedding_isRight_iff (i : Fin C.gapCount) :
    (∃ e, C.gapResourceEmbedding i = Sum.inr e) ↔
      ¬T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i)) := by
  classical
  by_cases h : T.Adj (C.outer (C.gapTop i)) (C.outer (C.gapBottom i))
  · simp [gapResourceEmbedding, h]
  · simp [gapResourceEmbedding, h]

end VerticalWestBareComb

end GridGraphs
