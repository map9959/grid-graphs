import Mathlib
import GridGraphs.Core.Defs
import GridGraphs.Core.Bounds
import GridGraphs.Core.Spanning
import GridGraphs.Forests.ForestExtension

/-!
# Lower-bound construction via the simple spine + column tree

For any `m, n ≥ 1`, the grid graph `gridGraph m n` admits a spanning
subtree built as

* Top row spine: `(0, c) — (0, c + 1)` for `c ∈ [0, n − 2]`.
* Per-column verticals: `(i, c) — (i + 1, c)` for `i ∈ [0, m − 2]` and
  every column `c`.

This tree has exactly `mn − 1` edges (count: `(n − 1) + n(m − 1)`), is
connected (every vertex reaches `(0, 0)` along its column then along the
top row), and is acyclic (proved here via the
`isTree_iff_connected_and_card` characterisation).

In this tree the entire **top row** is preserved (each `(0, c)` has
both its grid-horizontal neighbours and its vertical-down neighbour in
the tree). Hence `numPreserved ≥ n`.

By transposition, swapping `m` and `n` gives `numPreserved ≥ m`.
Combining: `max(m, n) ≤ maxPreserved m n`.

This achieves the simpler lower bound `lowerB m n = m + n − 2` only when
`min(m, n) ≤ 2`; for square grids with `m, n ≥ 3` the actual `P` is
strictly larger but is realised by smarter constructions (Phase 5 / 9).

The "L-bend" double comb that uniformly hits `m + n − 2` is documented in
`docs/DERIVATION.md` but its acyclicity proof in Lean is non-trivial
(requires explicit walk analysis or a tree-distance argument). This
module pursues the simpler construction in full; the L-bend is left as
future work.
-/

namespace GridGraphs

open SimpleGraph

/-! ## Top-spine + columns spanning tree -/

/-- Adjacency for the top-spine + columns spanning subgraph. -/
def topSpineColumnsAdj (m n : Nat) (v w : GridVertex m n) : Prop :=
  -- Top row spine
  (v.1.val = 0 ∧ w.1.val = 0 ∧
    (v.2.val + 1 = w.2.val ∨ w.2.val + 1 = v.2.val)) ∨
  -- Column verticals at every column
  (v.2 = w.2 ∧ (v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val))

instance (m n : Nat) (v w : GridVertex m n) :
    Decidable (topSpineColumnsAdj m n v w) := by
  unfold topSpineColumnsAdj; infer_instance

/-- The top-spine + columns subgraph, a candidate spanning tree. -/
def topSpineColumns (m n : Nat) : SimpleGraph (GridVertex m n) where
  Adj := topSpineColumnsAdj m n
  symm := by
    constructor
    intro v w h
    unfold topSpineColumnsAdj at *
    rcases h with ⟨h1, h2, hd⟩ | ⟨h1, hd⟩
    · refine Or.inl ⟨h2, h1, ?_⟩
      rcases hd with h | h
      · exact Or.inr h
      · exact Or.inl h
    · refine Or.inr ⟨h1.symm, ?_⟩
      rcases hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  loopless := by
    constructor
    intro v h
    unfold topSpineColumnsAdj at h
    rcases h with ⟨_, _, hd⟩ | ⟨_, hd⟩ <;>
    · rcases hd with h | h <;> exact Nat.succ_ne_self _ h

instance (m n : Nat) : DecidableRel (topSpineColumns m n).Adj := by
  intro v w
  show Decidable (topSpineColumnsAdj m n v w)
  infer_instance

/-- The top-spine + columns subgraph lies inside the grid graph. -/
lemma topSpineColumns_le_gridGraph (m n : Nat) :
    topSpineColumns m n ≤ gridGraph m n := by
  intro v w hvw
  show adjacent m n v w
  change topSpineColumnsAdj m n v w at hvw
  unfold topSpineColumnsAdj at hvw
  rcases hvw with ⟨hr1, hr2, hd⟩ | ⟨hcol, hd⟩
  · left; refine ⟨?_, hd⟩; apply Fin.ext; rw [hr1, hr2]
  · right; exact ⟨hcol, hd⟩

/-! ## Reachability in `topSpineColumns`

Every grid vertex is reachable from `(0, 0)` along the comb structure. -/

/-- Within a column `c`, every vertex `(i, c)` is reachable from `(0, c)`. -/
lemma topSpineColumns_reachable_in_column {m n : Nat} (hm : 1 ≤ m)
    (i : Nat) (hi : i < m) (c : Fin n) :
    (topSpineColumns m n).Reachable (⟨0, by omega⟩, c) (⟨i, hi⟩, c) := by
  induction i with
  | zero => exact Reachable.refl _
  | succ k ih =>
    have hk : k < m := by omega
    -- Walk from (0, c) to (k, c) by IH, then one edge from (k, c) to (k+1, c).
    have hreach_k := ih hk
    have hadj : (topSpineColumns m n).Adj (⟨k, hk⟩, c) (⟨k + 1, hi⟩, c) := by
      show topSpineColumnsAdj m n (⟨k, hk⟩, c) (⟨k + 1, hi⟩, c)
      unfold topSpineColumnsAdj
      right
      exact ⟨rfl, Or.inl rfl⟩
    exact hreach_k.trans hadj.reachable

/-- Along the top row, `(0, 0)` is reachable to `(0, c)` for any `c`. -/
lemma topSpineColumns_reachable_top_row {m n : Nat} (hm : 1 ≤ m)
    (c : Nat) (hc : c < n) :
    (topSpineColumns m n).Reachable
      (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨c, hc⟩) := by
  induction c with
  | zero => exact Reachable.refl _
  | succ k ih =>
    have hk : k < n := by omega
    have hreach_k := ih hk
    have hadj : (topSpineColumns m n).Adj
        ((⟨0, by omega⟩, ⟨k, hk⟩) : GridVertex m n)
        (⟨0, by omega⟩, ⟨k + 1, hc⟩) := by
      show topSpineColumnsAdj m n _ _
      unfold topSpineColumnsAdj
      left
      exact ⟨rfl, rfl, Or.inl rfl⟩
    exact hreach_k.trans hadj.reachable

/-- Every grid vertex is reachable from `(0, 0)` in `topSpineColumns`. -/
lemma topSpineColumns_reachable_from_origin {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (v : GridVertex m n) :
    (topSpineColumns m n).Reachable
      ((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex m n) v := by
  -- Walk: (0,0) → (0, v.2) along top spine, then (0, v.2) → (v.1, v.2) along column.
  have hr1 := topSpineColumns_reachable_top_row hm v.2.val v.2.isLt
  have hr2 := topSpineColumns_reachable_in_column hm v.1.val v.1.isLt v.2
  -- Convert v.2 = ⟨v.2.val, v.2.isLt⟩ via Fin.ext.
  have heq2 : (⟨v.2.val, v.2.isLt⟩ : Fin n) = v.2 := Fin.ext rfl
  have heq1 : (⟨v.1.val, v.1.isLt⟩ : Fin m) = v.1 := Fin.ext rfl
  rw [heq2] at hr1
  rw [heq1] at hr2
  -- Now hr2 : Reachable (⟨0, _⟩, v.2) (v.1, v.2). Convert to v.
  have hr2_eq : ((v.1, v.2) : GridVertex m n) = v := Prod.mk.eta
  rw [hr2_eq] at hr2
  exact hr1.trans hr2

/-- `topSpineColumns m n` is preconnected for `m, n ≥ 1`. -/
lemma topSpineColumns_preconnected {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (topSpineColumns m n).Preconnected := by
  intro v w
  have hv := topSpineColumns_reachable_from_origin hm hn v
  have hw := topSpineColumns_reachable_from_origin hm hn w
  exact hv.symm.trans hw

/-- `topSpineColumns m n` is connected for `m, n ≥ 1`. -/
lemma topSpineColumns_connected {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (topSpineColumns m n).Connected := by
  have : Nonempty (GridVertex m n) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  exact { preconnected := topSpineColumns_preconnected hm hn }

/-! ## Top-row preservation

Every top-row vertex `(0, c)` has its grid-neighbours all in
`topSpineColumns m n`, so it is preserved (full-degree). -/

/-- The top spine has degree pattern `1` (corner) / `2` (interior) /
`1` (corner) — agreeing with the grid's top-row degrees. -/
lemma topSpineColumns_degree_top {m n : Nat} (hm : 1 ≤ m) (_hn : 1 ≤ n)
    (c : Fin n) :
    (topSpineColumns m n).degree (⟨0, by omega⟩, c) =
      (gridGraph m n).degree (⟨0, by omega⟩, c) := by
  -- Both sides equal the same set of neighbours: horizontal in top row,
  -- and the vertical down to row 1 (if m ≥ 2).
  -- We exhibit equality of neighborFinset.
  have hSame : (topSpineColumns m n).neighborFinset (⟨0, by omega⟩, c) =
      (gridGraph m n).neighborFinset (⟨0, by omega⟩, c) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    constructor
    · intro h
      exact topSpineColumns_le_gridGraph m n h
    · -- Conversely: any grid-edge incident to (0, c) is in topSpineColumns.
      intro h
      change adjacent m n _ _ at h
      change topSpineColumnsAdj m n _ _
      unfold adjacent at h
      unfold topSpineColumnsAdj
      rcases h with ⟨hr, hd⟩ | ⟨hcol, hd⟩
      · -- Same row (row 0): horizontal edge along top spine.
        left
        refine ⟨rfl, ?_, hd⟩
        -- Goal: w.1.val = 0. We have hr : (⟨0, _⟩, c).1 = w.1.
        have hw : w.1.val = 0 := by
          have hh : (((⟨0, by omega⟩, c) : GridVertex m n).1).val = w.1.val :=
            congrArg Fin.val hr
          exact hh.symm
        exact hw
      · -- Same column: vertical edge.
        right
        exact ⟨hcol, hd⟩
  show ((topSpineColumns m n).neighborFinset _).card =
    ((gridGraph m n).neighborFinset _).card
  rw [hSame]

/-- All top-row vertices are preserved in `topSpineColumns m n`. -/
lemma topSpineColumns_preserves_top_row {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (c : Fin n) :
    isPreserved m n (topSpineColumns m n) ((⟨0, by omega⟩, c) : GridVertex m n) := by
  unfold isPreserved
  exact topSpineColumns_degree_top hm hn c

end GridGraphs
