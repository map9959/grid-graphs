import Mathlib
import GridGraphs.Defs
import GridGraphs.Bounds
import GridGraphs.Forced

/-!
# Spanning subtrees and the operational upper bound `P(m, n) ≤ basicUB m n`

This module formalises the bridge from the algebraic bound expressions in
`Bounds.lean` to the operational quantity
`numPreserved m n T` for a spanning subtree `T` of the grid graph.

Key ingredients (Phase 8 of `docs/ROADMAP.md`):

* `IsSpanningSubtree G T` — `T ≤ G` and `T.IsTree`.
* The identification `gridGraph m n = pathGraph m □ pathGraph n` from
  `Defs.lean` lets us inherit degree decomposition from mathlib's
  `degree_boxProd` and connectivity from `pathGraph_connected`.
* `pathGraph_degree` — closed form for the degree in a path graph.
* `gridGraph_degree` — closed form for the degree of any grid vertex.
* `gridGraph_card_edgeFinset` — the grid has `m * (n − 1) + n * (m − 1)`
  edges.
* `total_deficiency` — `∑ v, vertexDeficiency v = D m n` for any spanning
  subtree.
* `vertexDeficiency_le_three`, plus per-class caps for corner / border /
  interior vertices.
* `preserved_le_basicUB` — the headline operational upper bound.
-/

namespace GridGraphs

open Finset SimpleGraph

/-! ## Path-graph degree

`pathGraph n` has degree `0` if `n ≤ 1` (no neighbours), `1` at the
endpoints `0` and `n − 1`, and `2` everywhere in between. -/

/-- A `pathGraph` is locally finite via mathlib's generic `neighborSetFintype`,
once we have a `DecidableRel` for it. -/
instance pathGraph_decidableRel (n : Nat) :
    DecidableRel (pathGraph n).Adj := by
  intro u v
  rw [show (pathGraph n).Adj u v ↔ (u.val + 1 = v.val ∨ v.val + 1 = u.val)
        from pathGraph_adj]
  infer_instance

/-- Closed form for `pathGraph` degree at an interior vertex. -/
lemma pathGraph_degree_interior {n : Nat} (v : Fin n)
    (hv0 : v.val ≠ 0) (hv1 : v.val + 1 ≠ n) :
    (pathGraph n).degree v = 2 := by
  -- Neighbours are exactly v - 1 and v + 1.
  have hN : v.val + 1 < n := by have := v.isLt; omega
  have hP : v.val - 1 < n := by have := v.isLt; omega
  let u₁ : Fin n := ⟨v.val - 1, hP⟩
  let u₂ : Fin n := ⟨v.val + 1, hN⟩
  have hu1_ne_u2 : u₁ ≠ u₂ := by
    intro h
    have : v.val - 1 = v.val + 1 := congrArg Fin.val h
    omega
  have hadj1 : (pathGraph n).Adj v u₁ := by
    rw [pathGraph_adj]; right; show (v.val - 1) + 1 = v.val; omega
  have hadj2 : (pathGraph n).Adj v u₂ := by
    rw [pathGraph_adj]; left; rfl
  -- Build the neighborFinset explicitly.
  have hneighbor :
      (pathGraph n).neighborFinset v = ({u₁, u₂} : Finset (Fin n)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    rw [pathGraph_adj]
    constructor
    · rintro (h | h)
      · right
        apply Fin.ext
        show w.val = v.val + 1
        omega
      · left
        apply Fin.ext
        show w.val = v.val - 1
        omega
    · rintro (h | h)
      · right; rw [h]; show v.val - 1 + 1 = v.val; omega
      · left; rw [h]
  show ((pathGraph n).neighborFinset v).card = 2
  rw [hneighbor]
  rw [Finset.card_pair hu1_ne_u2]

/-- Closed form for `pathGraph` degree at an endpoint of a path of length ≥ 2. -/
lemma pathGraph_degree_left_end {n : Nat} (hn : 2 ≤ n)
    (v : Fin n) (hv : v.val = 0) :
    (pathGraph n).degree v = 1 := by
  -- Only neighbour is v + 1.
  have hN : v.val + 1 < n := by omega
  let u : Fin n := ⟨v.val + 1, hN⟩
  have hadj : (pathGraph n).Adj v u := by
    rw [pathGraph_adj]; left; rfl
  have hneighbor : (pathGraph n).neighborFinset v = ({u} : Finset (Fin n)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    rw [pathGraph_adj]
    constructor
    · rintro (h | h)
      · apply Fin.ext; show w.val = v.val + 1; omega
      · -- Then w.val + 1 = v.val = 0; impossible.
        exfalso; omega
    · intro h; left; rw [h]
  show ((pathGraph n).neighborFinset v).card = 1
  rw [hneighbor]
  simp

lemma pathGraph_degree_right_end {n : Nat} (hn : 2 ≤ n)
    (v : Fin n) (hv : v.val + 1 = n) :
    (pathGraph n).degree v = 1 := by
  -- Only neighbour is v - 1.
  have hP : v.val - 1 < n := by have := v.isLt; omega
  have hv_pos : v.val ≥ 1 := by omega
  let u : Fin n := ⟨v.val - 1, hP⟩
  have hadj : (pathGraph n).Adj v u := by
    rw [pathGraph_adj]; right; show (v.val - 1) + 1 = v.val; omega
  have hneighbor : (pathGraph n).neighborFinset v = ({u} : Finset (Fin n)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    rw [pathGraph_adj]
    constructor
    · rintro (h | h)
      · -- v.val + 1 = w.val ≤ n - 1, but v.val + 1 = n ⇒ w.val ≥ n, impossible.
        exfalso
        have := w.isLt; omega
      · apply Fin.ext; show w.val = v.val - 1; omega
    · intro h; right
      rw [h]; show v.val - 1 + 1 = v.val; omega
  show ((pathGraph n).neighborFinset v).card = 1
  rw [hneighbor]
  simp

/-- The 1-vertex path graph has all degrees `0`. -/
lemma pathGraph_degree_one {v : Fin 1} : (pathGraph 1).degree v = 0 := by
  -- v.val = 0; no neighbours.
  show ((pathGraph 1).neighborFinset v).card = 0
  rw [Finset.card_eq_zero]
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
  rw [pathGraph_adj]
  intro h
  have := v.isLt
  have := w.isLt
  omega

/-! ## Grid degree

Inherits from `degree_boxProd`. -/

/-- Closed form for the grid-graph degree at any vertex, valid for
`m, n ≥ 1`. The two summands correspond to the row and column path graphs. -/
lemma gridGraph_degree (m n : Nat) (v : GridVertex m n) :
    (gridGraph m n).degree v
      = (pathGraph m).degree v.1 + (pathGraph n).degree v.2 := by
  -- Use the boxProd identification at the level of neighbour finsets.
  have hAdj : ∀ w, (gridGraph m n).Adj v w ↔ (pathGraph m □ pathGraph n).Adj v w := by
    intro w
    rw [gridGraph_eq_boxProd]
  have hSet : (gridGraph m n).neighborFinset v
      = (pathGraph m □ pathGraph n).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact hAdj w
  show ((gridGraph m n).neighborFinset v).card
      = (pathGraph m).degree v.1 + (pathGraph n).degree v.2
  rw [hSet]
  exact degree_boxProd v

/-- Grid degree is at most 4. -/
lemma gridGraph_degree_le_four (m n : Nat) (v : GridVertex m n) :
    (gridGraph m n).degree v ≤ 4 := by
  rw [gridGraph_degree]
  -- Show each pathGraph degree ≤ 2.
  have h1 : (pathGraph m).degree v.1 ≤ 2 := by
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- m ≤ 1, so v.1 is `Fin 0` (impossible) or `Fin 1` (degree 0).
      interval_cases m
      · exact v.1.elim0
      · rw [pathGraph_degree_one]; omega
    · by_cases hv0 : v.1.val = 0
      · rw [pathGraph_degree_left_end hm v.1 hv0]; omega
      · by_cases hvN : v.1.val + 1 = m
        · rw [pathGraph_degree_right_end hm v.1 hvN]; omega
        · rw [pathGraph_degree_interior v.1 hv0 hvN]
  have h2 : (pathGraph n).degree v.2 ≤ 2 := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact v.2.elim0
      · rw [pathGraph_degree_one]; omega
    · by_cases hv0 : v.2.val = 0
      · rw [pathGraph_degree_left_end hn v.2 hv0]; omega
      · by_cases hvN : v.2.val + 1 = n
        · rw [pathGraph_degree_right_end hn v.2 hvN]; omega
        · rw [pathGraph_degree_interior v.2 hv0 hvN]
  omega

/-- Per-class grid degree: corner vertex (`m, n ≥ 2`). -/
lemma gridGraph_degree_corner {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n)
    (h1 : v.1.val = 0 ∨ v.1.val + 1 = m)
    (h2 : v.2.val = 0 ∨ v.2.val + 1 = n) :
    (gridGraph m n).degree v = 2 := by
  rw [gridGraph_degree]
  have hp : (pathGraph m).degree v.1 = 1 := by
    rcases h1 with h | h
    · exact pathGraph_degree_left_end hm v.1 h
    · exact pathGraph_degree_right_end hm v.1 h
  have hq : (pathGraph n).degree v.2 = 1 := by
    rcases h2 with h | h
    · exact pathGraph_degree_left_end hn v.2 h
    · exact pathGraph_degree_right_end hn v.2 h
  rw [hp, hq]

/-- Per-class grid degree: border (non-corner) vertex `(m, n ≥ 2)`. -/
lemma gridGraph_degree_border {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n)
    (h : ((v.1.val = 0 ∨ v.1.val + 1 = m) ∧ ¬ (v.2.val = 0 ∨ v.2.val + 1 = n))
       ∨ (¬ (v.1.val = 0 ∨ v.1.val + 1 = m) ∧ (v.2.val = 0 ∨ v.2.val + 1 = n))) :
    (gridGraph m n).degree v = 3 := by
  rw [gridGraph_degree]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · push_neg at h2
    obtain ⟨hv0, hvN⟩ := h2
    have hp : (pathGraph m).degree v.1 = 1 := by
      rcases h1 with h | h
      · exact pathGraph_degree_left_end hm v.1 h
      · exact pathGraph_degree_right_end hm v.1 h
    have hq : (pathGraph n).degree v.2 = 2 :=
      pathGraph_degree_interior v.2 hv0 hvN
    rw [hp, hq]
  · push_neg at h1
    obtain ⟨hv0, hvN⟩ := h1
    have hp : (pathGraph m).degree v.1 = 2 :=
      pathGraph_degree_interior v.1 hv0 hvN
    have hq : (pathGraph n).degree v.2 = 1 := by
      rcases h2 with h | h
      · exact pathGraph_degree_left_end hn v.2 h
      · exact pathGraph_degree_right_end hn v.2 h
    rw [hp, hq]

/-- Per-class grid degree: interior vertex (with both rows and columns away
from the boundary; the `m, n ≥ 2` hypotheses are kept for caller convenience
even though the proof doesn't need them). -/
lemma gridGraph_degree_interior {m n : Nat} (_hm : 2 ≤ m) (_hn : 2 ≤ n)
    (v : GridVertex m n)
    (h1 : ¬ (v.1.val = 0 ∨ v.1.val + 1 = m))
    (h2 : ¬ (v.2.val = 0 ∨ v.2.val + 1 = n)) :
    (gridGraph m n).degree v = 4 := by
  rw [gridGraph_degree]
  push_neg at h1 h2
  obtain ⟨hv10, hv1N⟩ := h1
  obtain ⟨hv20, hv2N⟩ := h2
  rw [pathGraph_degree_interior v.1 hv10 hv1N,
      pathGraph_degree_interior v.2 hv20 hv2N]

/-! ## Grid edge count -/

/-- The number of edges in `pathGraph k` equals `k - 1`. -/
lemma pathGraph_card_edgeFinset (k : Nat) : (pathGraph k).edgeFinset.card = k - 1 := by
  -- 2 * #edges = ∑ v, degree v.
  -- For k = 0: empty graph, 0 edges. For k = 1: degree 0 everywhere, 0 edges.
  -- For k ≥ 2: 2 endpoint vertices contribute 1 each, k-2 interior contribute 2 each.
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · -- k = 0, no vertices.
      simp
    · -- k = 1, single vertex, no edges.
      have h2c : 2 * (pathGraph 1).edgeFinset.card = 0 := by
        rw [← (pathGraph 1).sum_degrees_eq_twice_card_edges]
        rw [Finset.sum_congr rfl (fun v _ => pathGraph_degree_one (v := v))]
        simp
      omega
  · -- k ≥ 2: split sum into endpoints and interior.
    have h2c : 2 * (pathGraph k).edgeFinset.card = 2 * (k - 1) := by
      rw [← (pathGraph k).sum_degrees_eq_twice_card_edges]
      -- ∑ v, degree v = 2 * (k - 1).
      have hsum : ∑ v : Fin k, (pathGraph k).degree v = 2 * (k - 1) := by
        -- Split univ = {endpoints} ∪ {interior}.
        let endpoints : Finset (Fin k) :=
          (Finset.univ : Finset (Fin k)).filter
            (fun v => v.val = 0 ∨ v.val + 1 = k)
        let interior : Finset (Fin k) :=
          (Finset.univ : Finset (Fin k)).filter
            (fun v => ¬ (v.val = 0 ∨ v.val + 1 = k))
        have huniv : (Finset.univ : Finset (Fin k)) = endpoints ∪ interior := by
          ext v
          simp only [endpoints, interior, Finset.mem_univ, Finset.mem_union,
            Finset.mem_filter, true_and]
          tauto
        have hdisj : Disjoint endpoints interior := by
          rw [Finset.disjoint_filter]
          intros _ _ hp hq; exact hq hp
        have hsplit :
            ∑ v : Fin k, (pathGraph k).degree v
              = (∑ v ∈ endpoints, (pathGraph k).degree v)
                + ∑ v ∈ interior, (pathGraph k).degree v := by
          rw [huniv, Finset.sum_union hdisj]
        rw [hsplit]
        -- Each endpoint contributes 1.
        have h_end : ∀ v ∈ endpoints, (pathGraph k).degree v = 1 := by
          intro v hv
          simp only [endpoints, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases hv with h | h
          · exact pathGraph_degree_left_end hk v h
          · exact pathGraph_degree_right_end hk v h
        -- Each interior vertex contributes 2.
        have h_int : ∀ v ∈ interior, (pathGraph k).degree v = 2 := by
          intro v hv
          simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          push_neg at hv
          obtain ⟨hv0, hvN⟩ := hv
          exact pathGraph_degree_interior v hv0 hvN
        rw [Finset.sum_congr rfl h_end, Finset.sum_congr rfl h_int]
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
        -- Compute |endpoints| = 2 (for k ≥ 2) and |interior| = k - 2.
        have hcard_end : endpoints.card = 2 := by
          have h0 : (0 : Nat) < k := by omega
          have hN : (k - 1 : Nat) < k := by omega
          have heq : endpoints = ({⟨0, h0⟩, ⟨k - 1, hN⟩} : Finset (Fin k)) := by
            ext v
            simp only [endpoints, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (h | h)
              · left; apply Fin.ext; exact h
              · right; apply Fin.ext; show v.val = k - 1; omega
            · rintro (h | h)
              · left; rw [h]
              · right; rw [h]; show k - 1 + 1 = k; omega
          rw [heq]
          rw [Finset.card_pair]
          intro h
          have : (0 : Nat) = k - 1 := congrArg Fin.val h
          omega
        have hcard_int : interior.card = k - 2 := by
          have h_total : endpoints.card + interior.card = k := by
            have : endpoints.card + interior.card
                = (Finset.univ : Finset (Fin k)).card := by
              rw [huniv, Finset.card_union_of_disjoint hdisj]
            rw [this]; simp
          omega
        rw [hcard_end, hcard_int]
        -- 2 * 1 + (k - 2) * 2 = 2 * (k - 1).
        omega
      rw [hsum]
    omega

/-- The number of edges of `gridGraph m n` equals `numEdges m n`. Proved
via the degree-sum formula. -/
lemma gridGraph_card_edgeFinset (m n : Nat) :
    2 * (gridGraph m n).edgeFinset.card = 2 * numEdges m n := by
  -- 2 * #edges = ∑ v, degree v.
  rw [← (gridGraph m n).sum_degrees_eq_twice_card_edges]
  -- Compute the degree sum by replacing each summand via `gridGraph_degree`.
  have hCongr : ∀ (v : GridVertex m n), v ∈ (Finset.univ : Finset (GridVertex m n)) →
      (gridGraph m n).degree v
        = (pathGraph m).degree v.1 + (pathGraph n).degree v.2 :=
    fun v _ => gridGraph_degree m n v
  rw [Finset.sum_congr rfl hCongr]
  -- Distribute the sum.
  rw [Finset.sum_add_distrib]
  -- Convert each ∑ v : Fin m × Fin n, ... to ∑ a, ∑ b, ... .
  rw [show (∑ v : GridVertex m n, (pathGraph m).degree v.1)
        = ∑ a : Fin m, ∑ _ : Fin n, (pathGraph m).degree a from
      Fintype.sum_prod_type' (fun a _ => (pathGraph m).degree a)]
  rw [show (∑ v : GridVertex m n, (pathGraph n).degree v.2)
        = ∑ _ : Fin m, ∑ b : Fin n, (pathGraph n).degree b from
      Fintype.sum_prod_type' (fun _ b => (pathGraph n).degree b)]
  -- Reduce both inner sums by Finset.sum_const + simp, then pull constants
  -- out of the row-degree outer sum.
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- Goal is now: ∑ x, n * (pathGraph m).degree x + m * ∑ b, ... = 2 * numEdges m n.
  rw [← Finset.mul_sum]
  -- Apply the path-graph degree-sum formula and edge count.
  rw [(pathGraph m).sum_degrees_eq_twice_card_edges]
  rw [(pathGraph n).sum_degrees_eq_twice_card_edges]
  rw [pathGraph_card_edgeFinset, pathGraph_card_edgeFinset]
  -- Goal: n * (2 * (m - 1)) + m * (2 * (n - 1)) = 2 * numEdges m n.
  unfold numEdges numHoriz numVert
  ring

/-! ## `IsSpanningSubtree` predicate -/

/-- `T` is a spanning subtree of `G` iff `T ≤ G` and `T` is a tree. -/
def IsSpanningSubtree {V : Type*} (G T : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree

namespace IsSpanningSubtree

variable {V : Type*} {G T : SimpleGraph V}

lemma le (h : IsSpanningSubtree G T) : T ≤ G := h.1
lemma isTree (h : IsSpanningSubtree G T) : T.IsTree := h.2
lemma isAcyclic (h : IsSpanningSubtree G T) : T.IsAcyclic := h.2.IsAcyclic
lemma isConnected (h : IsSpanningSubtree G T) : T.Connected := h.2.isConnected

/-- Per-vertex degree monotonicity: `T.degree v ≤ G.degree v`. -/
lemma degree_le [Fintype V] [DecidableRel T.Adj] [DecidableRel G.Adj]
    (h : IsSpanningSubtree G T) (v : V) :
    T.degree v ≤ G.degree v :=
  T.degree_le_of_le h.le

/-- Tree edge count `|E(T)| = |V| − 1`. -/
lemma card_edgeFinset [Fintype V] [DecidableRel T.Adj]
    (h : IsSpanningSubtree G T) :
    T.edgeFinset.card + 1 = Fintype.card V :=
  h.isTree.card_edgeFinset

/-- Tree degree-sum identity: `∑ v, T.degree v = 2 * (|V| − 1)`. -/
lemma sum_degrees [Fintype V] [DecidableRel T.Adj]
    (h : IsSpanningSubtree G T) :
    ∑ v, T.degree v = 2 * (Fintype.card V - 1) := by
  rw [T.sum_degrees_eq_twice_card_edges]
  have hc := h.card_edgeFinset (V := V)
  omega

end IsSpanningSubtree

/-! ## Total deficiency identity -/

/-- Sum of `(gridGraph m n).degree v` over all vertices equals `2 * numEdges m n`. -/
lemma sum_gridGraph_degree (m n : Nat) :
    ∑ v : GridVertex m n, (gridGraph m n).degree v = 2 * numEdges m n := by
  rw [(gridGraph m n).sum_degrees_eq_twice_card_edges]
  -- Multiply both sides by 1 to match gridGraph_card_edgeFinset's `2 * _` form.
  have h := gridGraph_card_edgeFinset m n
  omega

/-- For any spanning subtree `T` of `gridGraph m n`, the sum of per-vertex
deficiencies equals `D m n = 2 (m-1)(n-1)`. -/
theorem total_deficiency {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    ∑ v, vertexDeficiency m n T v = D m n := by
  unfold vertexDeficiency
  -- Distribute the Nat subtraction across the sum.
  rw [Finset.sum_tsub_distrib (s := (Finset.univ : Finset (GridVertex m n)))
        (f := fun v => (gridGraph m n).degree v) (g := fun v => T.degree v)
        (fun v _ => hT.degree_le v)]
  rw [sum_gridGraph_degree]
  rw [hT.sum_degrees]
  -- Goal: 2 * numEdges m n - 2 * (Fintype.card (GridVertex m n) - 1) = D m n.
  rw [show (Fintype.card (GridVertex m n) : Nat) = m * n from by
        unfold GridVertex; simp [Fintype.card_prod]]
  unfold D numEdges numHoriz numVert
  -- Use D_eq_deficiency-style algebra. After unfolding, the LHS is
  -- 2 * (m * (n-1) + n * (m-1)) - 2 * (m * n - 1).
  -- For m, n ≥ 1 this simplifies to 2 * (m-1) * (n-1).
  -- For m = 0 or n = 0, both sides are 0 (handled by Nat-subtraction zeroing).
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · simp [hm0]
  · rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp [hn0]
    · -- m, n ≥ 1: write m = m'+1, n = n'+1 and compute.
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨m', rfl⟩
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨n', rfl⟩
      show 2 * ((m' + 1) * ((n' + 1) - 1) + (n' + 1) * ((m' + 1) - 1))
            - 2 * ((m' + 1) * (n' + 1) - 1)
        = 2 * ((m' + 1) - 1) * ((n' + 1) - 1)
      have hsub_m : (m' + 1) - 1 = m' := by omega
      have hsub_n : (n' + 1) - 1 = n' := by omega
      rw [hsub_m, hsub_n]
      have hsub_mn : (m' + 1) * (n' + 1) - 1 = m' * n' + m' + n' := by
        have : (m' + 1) * (n' + 1) = m' * n' + m' + n' + 1 := by ring
        omega
      rw [hsub_mn]
      -- Now: 2*((m'+1)*n' + (n'+1)*m') - 2*(m'*n' + m' + n') = 2*m'*n'.
      -- Expand both products via separate identities.
      have he1 : (m' + 1) * n' = m' * n' + n' := by ring
      have he2 : (n' + 1) * m' = m' * n' + m' := by ring
      have heq : 2 * ((m' + 1) * n' + (n' + 1) * m')
            = 4 * (m' * n') + 2 * m' + 2 * n' := by
        rw [he1, he2]; ring
      rw [heq]
      -- Goal: 4 * m'n' + 2m' + 2n' - 2 * (m' * n' + m' + n') = 2 * m' * n'.
      -- Group LHS: = 4 * m'n' + 2m' + 2n' - 2m'n' - 2m' - 2n' = 2 * m'n'.
      have : 2 * (m' * n' + m' + n') = 2 * (m' * n') + 2 * m' + 2 * n' := by ring
      rw [this]
      have hgoal : 2 * m' * n' = 2 * (m' * n') := by ring
      rw [hgoal]
      omega

/-! ## Per-vertex deficiency caps -/

/-- The grid graph has every vertex of `T` adjacent to ≥ 1 neighbour, provided
`m, n ≥ 1` and `m * n ≥ 2`. (For `m = n = 1`, the only vertex is its own
unique component and every spanning tree is empty.) -/
lemma tree_degree_pos {m n : Nat} (hmn : 2 ≤ m * n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n) :
    1 ≤ T.degree v := by
  -- `T` is connected; pick any other vertex and follow the walk one step.
  have hConn : T.Connected := hT.isConnected
  -- There exists w ≠ v in V (since |V| ≥ 2).
  have hVcard : 2 ≤ Fintype.card (GridVertex m n) := by
    rw [show (Fintype.card (GridVertex m n) : Nat) = m * n from by
          unfold GridVertex; simp [Fintype.card_prod]]
    exact hmn
  obtain ⟨w, hw⟩ : ∃ w : GridVertex m n, w ≠ v := by
    by_contra hno
    push_neg at hno
    have : ∀ w : GridVertex m n, w = v := hno
    -- All vertices equal v ⇒ |V| ≤ 1, contradiction.
    have hSubset : (Finset.univ : Finset (GridVertex m n)) ⊆ {v} := by
      intro w _
      rw [this w]; simp
    have hcard : (Finset.univ : Finset (GridVertex m n)).card ≤ 1 := by
      calc (Finset.univ : Finset (GridVertex m n)).card
            ≤ ({v} : Finset (GridVertex m n)).card :=
              Finset.card_le_card hSubset
          _ = 1 := Finset.card_singleton v
    have : Fintype.card (GridVertex m n) ≤ 1 := by
      rw [← Finset.card_univ]; exact hcard
    omega
  -- T is connected, so there's a walk v ⤳ w; this walk has at least one edge,
  -- so v has at least one T-neighbour.
  have hReach : T.Reachable v w := hConn.preconnected v w
  obtain ⟨p⟩ := hReach
  -- The walk from v to w has length ≥ 1 since v ≠ w.
  -- Cases on `p`: nil ⇒ v = w (contradiction); cons gives an adjacency.
  cases p with
  | nil => exact absurd rfl hw.symm
  | @cons _ b _ hadj _ =>
    -- The first edge gives an adjacency v ~ b.
    have hmem : b ∈ T.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]; exact hadj
    show 1 ≤ (T.neighborFinset v).card
    exact Finset.card_pos.mpr ⟨b, hmem⟩

/-- Per-vertex deficiency cap: at most 3 for `m, n ≥ 2`. -/
theorem vertexDeficiency_le_three {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n) :
    vertexDeficiency m n T v ≤ 3 := by
  unfold vertexDeficiency
  have h1 : (gridGraph m n).degree v ≤ 4 := gridGraph_degree_le_four m n v
  have h2 : 1 ≤ T.degree v := tree_degree_pos (by nlinarith) hT v
  omega

/-- Per-class deficiency cap: corner vertex absorbs ≤ 1 deficiency. -/
theorem vertexDeficiency_le_one_of_corner {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n)
    (h1 : v.1.val = 0 ∨ v.1.val + 1 = m)
    (h2 : v.2.val = 0 ∨ v.2.val + 1 = n) :
    vertexDeficiency m n T v ≤ 1 := by
  unfold vertexDeficiency
  rw [gridGraph_degree_corner hm hn v h1 h2]
  have hT_pos : 1 ≤ T.degree v := tree_degree_pos (by nlinarith) hT v
  omega

/-- Per-class deficiency cap: non-corner border vertex absorbs ≤ 2 deficiency. -/
theorem vertexDeficiency_le_two_of_border {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n)
    (h : ((v.1.val = 0 ∨ v.1.val + 1 = m) ∧ ¬ (v.2.val = 0 ∨ v.2.val + 1 = n))
       ∨ (¬ (v.1.val = 0 ∨ v.1.val + 1 = m) ∧ (v.2.val = 0 ∨ v.2.val + 1 = n))) :
    vertexDeficiency m n T v ≤ 2 := by
  unfold vertexDeficiency
  rw [gridGraph_degree_border hm hn v h]
  have hT_pos : 1 ≤ T.degree v := tree_degree_pos (by nlinarith) hT v
  omega

/-! ## Headline upper bound: `numPreserved ≤ basicUB` -/

/-- The number of preserved vertices in any spanning subtree of the grid graph
is at most the basic algebraic upper bound `basicUB m n`. -/
theorem preserved_le_basicUB {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    numPreserved m n T ≤ basicUB m n := by
  -- Special-case strips first: m = 1 or n = 1 ⇒ D = 0, basicUB = m * n.
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- m = 1.
    have hm_eq : m = 1 := by omega
    have hD : D m n = 0 := by
      unfold D; rw [hm_eq]; simp
    have hUB : basicUB m n = m * n := by
      unfold basicUB; rw [hD]; simp
    rw [hUB]
    -- numPreserved ≤ |univ| = m * n.
    unfold numPreserved
    calc ((Finset.univ : Finset (GridVertex m n)).filter
            (fun v => isPreserved m n T v)).card
        ≤ (Finset.univ : Finset (GridVertex m n)).card :=
          Finset.card_filter_le _ _
      _ = m * n := by
          unfold GridVertex
          simp [Fintype.card_prod]
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- n = 1.
    have hn_eq : n = 1 := by omega
    have hD : D m n = 0 := by
      unfold D; rw [hn_eq]; simp
    have hUB : basicUB m n = m * n := by
      unfold basicUB; rw [hD]; simp
    rw [hUB]
    unfold numPreserved
    calc ((Finset.univ : Finset (GridVertex m n)).filter
            (fun v => isPreserved m n T v)).card
        ≤ (Finset.univ : Finset (GridVertex m n)).card :=
          Finset.card_filter_le _ _
      _ = m * n := by
          unfold GridVertex
          simp [Fintype.card_prod]
  -- Main case: m, n ≥ 2.
  -- Bound D = ∑ v, vertexDeficiency v ≥ ∑ v ∈ U, vertexDeficiency v
  --       ≥ 1 * (number of non-preserved vertices) (vertexDeficiency v ≥ 1
  --         for non-preserved). And ≤ 3 * |U|. We use the upper bound only.
  -- |P| = numPreserved = m*n - |U|, so |U| = m*n - |P| ≥ ⌈D/3⌉, i.e.
  -- |P| ≤ m*n - ⌈D/3⌉ = basicUB m n.
  have hTotal : ∑ v, vertexDeficiency m n T v = D m n :=
    total_deficiency hT
  -- Bound D ≤ 3 * |U|.
  have hCap : ∀ v ∈ (Finset.univ : Finset (GridVertex m n)),
      vertexDeficiency m n T v ≤ 3 :=
    fun v _ => vertexDeficiency_le_three hm2 hn2 hT v
  have hSum_le : ∑ v, vertexDeficiency m n T v
      ≤ ∑ _v : GridVertex m n, 3 :=
    Finset.sum_le_sum hCap
  -- Restrict the sum to the non-preserved set.
  have hPreserved_zero : ∀ v ∈ (Finset.univ : Finset (GridVertex m n)),
      isPreserved m n T v → vertexDeficiency m n T v = 0 := by
    intros v _ hv
    unfold vertexDeficiency isPreserved at *
    omega
  -- Build U = univ \ preserved set.
  set P : Finset (GridVertex m n) :=
    (Finset.univ : Finset (GridVertex m n)).filter (fun v => isPreserved m n T v)
  set U : Finset (GridVertex m n) :=
    (Finset.univ : Finset (GridVertex m n)).filter (fun v => ¬ isPreserved m n T v)
  have hPU_card : P.card + U.card = m * n := by
    have : P.card + U.card = (Finset.univ : Finset (GridVertex m n)).card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    rw [this]
    unfold GridVertex; simp [Fintype.card_prod]
  -- ∑ v, vertexDeficiency = ∑ v ∈ P, ... + ∑ v ∈ U, ... = 0 + ∑ v ∈ U, ...
  have hSplit : ∑ v, vertexDeficiency m n T v
      = ∑ v ∈ U, vertexDeficiency m n T v := by
    have hSplit_full :
        ∑ v, vertexDeficiency m n T v
          = (∑ v ∈ P, vertexDeficiency m n T v)
            + ∑ v ∈ U, vertexDeficiency m n T v := by
      have hUniv : (Finset.univ : Finset (GridVertex m n)) = P ∪ U := by
        ext v
        simp only [P, U, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
        exact ⟨fun _ => Or.elim (em (isPreserved m n T v)) Or.inl Or.inr,
               fun _ => trivial⟩
      have hDisj : Disjoint P U := by
        rw [Finset.disjoint_filter]; intros _ _ hp hq; exact hq hp
      rw [hUniv, Finset.sum_union hDisj]
    have hP_zero : ∑ v ∈ P, vertexDeficiency m n T v = 0 := by
      apply Finset.sum_eq_zero
      intros v hv
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      unfold vertexDeficiency isPreserved at *
      omega
    rw [hSplit_full, hP_zero]; simp
  -- ∑ v ∈ U, vertexDeficiency v ≤ ∑ v ∈ U, 3 = 3 * |U|.
  have hU_le : ∑ v ∈ U, vertexDeficiency m n T v ≤ 3 * U.card := by
    calc ∑ v ∈ U, vertexDeficiency m n T v
        ≤ ∑ v ∈ U, 3 :=
          Finset.sum_le_sum (fun v _ => vertexDeficiency_le_three hm2 hn2 hT v)
      _ = 3 * U.card := by simp [Finset.sum_const, mul_comm]
  -- Combine: D = ∑ ≤ 3 * |U|.
  have hD_le_3U : D m n ≤ 3 * U.card := by
    rw [← hTotal, hSplit]; exact hU_le
  -- |P| = numPreserved m n T.
  have hP_eq : P.card = numPreserved m n T := rfl
  -- Final arithmetic: |P| ≤ basicUB m n.
  unfold basicUB
  -- basicUB = m*n - ceilDiv3 (D m n).
  -- Need: |P| ≤ m*n - ceilDiv3 D, i.e. |P| + ceilDiv3 D ≤ m*n.
  -- Since 3 * ceilDiv3 D ≥ D and D ≤ 3 * |U|:
  --   3 * ceilDiv3 D ≥ D, so ceilDiv3 D ≤ |U| + 1? Not quite.
  -- Better: 3 * (m*n - |P|) = 3 * |U| ≥ D, so m*n - |P| ≥ D/3,
  -- but ceilDiv3 = ⌈D/3⌉ may be one more.
  -- Concretely: 3 * ceilDiv3 D ≤ D + 2 ≤ 3 * |U| + 2.
  -- So ceilDiv3 D ≤ |U|; then |P| = m*n - |U| ≤ m*n - ceilDiv3 D = basicUB.
  -- Need a sharper bound. Use `ceilDiv3_mul_le`:
  --   3 * ceilDiv3 D ≤ D + 2.
  have hCeil_lo : 3 * ceilDiv3 (D m n) ≤ D m n + 2 := ceilDiv3_mul_le _
  have hCeil_le_U : ceilDiv3 (D m n) ≤ U.card := by
    -- 3 * ceilDiv3 D ≤ D + 2 ≤ 3 * |U| + 2 ⇒ ceilDiv3 D ≤ |U| + 2/3, so ≤ |U|.
    -- omega should handle this from hCeil_lo, hD_le_3U.
    omega
  -- Conclude |P| ≤ m*n - ceilDiv3 D.
  rw [← hP_eq]
  have hP_le : P.card ≤ m * n - ceilDiv3 (D m n) := by
    have hD_nonneg : ceilDiv3 (D m n) ≤ m * n := by
      have := ceilDiv3_D_le_mn hm hn
      exact this
    omega
  exact hP_le

/-- Universal form of the headline upper bound: any spanning subtree of the
grid graph has at most `basicUB m n` preserved vertices. -/
theorem forall_spanning_subtree_preserved_le_basicUB
    {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∀ (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph m n) T → numPreserved m n T ≤ basicUB m n :=
  fun _ _ hT => preserved_le_basicUB hm hn hT

end GridGraphs
