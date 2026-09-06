import GridGraphs.Core.ForcedMaximum
import GridGraphs.Constructions.DoubleComb

/-!
# Width-four lower bound

The top and bottom rows of a `4 x n` grid force two disjoint combs.  We embed
those combs into consecutive halves of the acyclic top-spine comb on
`2 x (2n)` vertices.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The top and bottom rows of a width-four grid. -/
def widthFourOuterRows (n : Nat) : Finset (GridVertex 4 n) :=
  ({⟨0, by omega⟩, ⟨3, by omega⟩} : Finset (Fin 4)) ×ˢ Finset.univ

@[simp] theorem mem_widthFourOuterRows {n : Nat} (v : GridVertex 4 n) :
    v ∈ widthFourOuterRows n ↔ v.1.val = 0 ∨ v.1.val = 3 := by
  unfold widthFourOuterRows
  rw [Finset.mem_product]
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, and_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  · rintro (h | h)
    · apply Or.inl
      apply Fin.ext
      simpa using h
    · apply Or.inr
      apply Fin.ext
      simpa using h

@[simp] theorem card_widthFourOuterRows (n : Nat) :
    (widthFourOuterRows n).card = 2 * n := by
  have hrows : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Finset (Fin 4)).card = 2 := by
    decide
  rw [widthFourOuterRows, Finset.card_product, hrows]
  simp

/-- Every lower-row vertex of the top-spine comb has only its vertical edge. -/
private theorem topSpineColumns_degree_lower {N : Nat} (c : Fin N) :
    (topSpineColumns 2 N).degree ((⟨1, by omega⟩, c) : GridVertex 2 N) = 1 := by
  let u : GridVertex 2 N := (⟨0, by omega⟩, c)
  have hneighbors :
      (topSpineColumns 2 N).neighborFinset ((⟨1, by omega⟩, c) : GridVertex 2 N) =
        {u} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro h
      change topSpineColumnsAdj 2 N _ _ at h
      rcases h with h | h
      · exact (by rcases h with ⟨hr, _⟩; norm_num at hr)
      · rcases h with ⟨hc, hr⟩
        apply Prod.ext
        · apply Fin.ext
          dsimp [u]
          rcases hr with hr | hr
          · have hw := w.1.isLt
            norm_num at hr
            omega
          · have hw := w.1.isLt
            norm_num at hr
            omega
        · apply Fin.ext
          exact congrArg Fin.val hc.symm
    · intro h
      subst w
      change topSpineColumnsAdj 2 N _ _
      exact Or.inr ⟨rfl, Or.inr rfl⟩
  change ((topSpineColumns 2 N).neighborFinset _).card = 1
  rw [hneighbors]
  simp

/-- The top-spine comb on two rows is a tree. -/
private theorem topSpineColumns_two_isTree {N : Nat} (hN : 1 ≤ N) :
    (topSpineColumns 2 N).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨topSpineColumns_connected (by omega) hN, ?_⟩
  have htop (c : Fin N) :
      (topSpineColumns 2 N).degree ((⟨0, by omega⟩, c) : GridVertex 2 N) =
        (pathGraph N).degree c + 1 := by
    change (topSpineColumns 2 N).degree ((⟨0, by omega⟩, c) : GridVertex 2 N) =
      (pathGraph N).degree c + 1
    rw [topSpineColumns_degree_top (by omega) hN, gridGraph_degree]
    have hrow : (pathGraph 2).degree (⟨0, by omega⟩ : Fin 2) = 1 :=
      pathGraph_degree_left_end (by omega) _ rfl
    rw [hrow]
    change 1 + (pathGraph N).degree c = (pathGraph N).degree c + 1
    omega
  have hsumPath : ∑ c : Fin N, (pathGraph N).degree c = 2 * (N - 1) := by
    rw [(pathGraph N).sum_degrees_eq_twice_card_edges, pathGraph_card_edgeFinset]
  have hsum : ∑ v : GridVertex 2 N, (topSpineColumns 2 N).degree v =
      2 * (2 * N - 1) := by
    rw [show (∑ v : GridVertex 2 N, (topSpineColumns 2 N).degree v) =
        ∑ i : Fin 2, ∑ c : Fin N, (topSpineColumns 2 N).degree (i, c) from
      Fintype.sum_prod_type' (fun i c => (topSpineColumns 2 N).degree (i, c))]
    have hzero : (∑ c : Fin N,
        (topSpineColumns 2 N).degree ((⟨0, by omega⟩, c) : GridVertex 2 N)) =
        2 * (N - 1) + N := by
      simp_rw [htop]
      rw [Finset.sum_add_distrib, hsumPath]
      simp
    have hone : (∑ c : Fin N,
        (topSpineColumns 2 N).degree ((⟨1, by omega⟩, c) : GridVertex 2 N)) = N := by
      simp_rw [topSpineColumns_degree_lower]
      simp
    rw [Fin.sum_univ_two]
    change (∑ c : Fin N,
        (topSpineColumns 2 N).degree ((⟨0, by omega⟩, c) : GridVertex 2 N)) +
      (∑ c : Fin N,
        (topSpineColumns 2 N).degree ((⟨1, by omega⟩, c) : GridVertex 2 N)) = _
    rw [hzero, hone]
    omega
  have hedge : (topSpineColumns 2 N).edgeFinset.card = 2 * N - 1 := by
    have hdegrees := (topSpineColumns 2 N).sum_degrees_eq_twice_card_edges
    rw [hsum] at hdegrees
    omega
  calc
    Nat.card (topSpineColumns 2 N).edgeSet + 1 =
        (topSpineColumns 2 N).edgeFinset.card + 1 := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
    _ = 2 * N := by rw [hedge]; omega
    _ = Nat.card (GridVertex 2 N) := by
      rw [Nat.card_eq_fintype_card]
      simp [GridVertex, Fintype.card_prod]

/-- Place the upper and lower forced combs in the two halves of one comb. -/
private def widthFourCombEmbedding {n : Nat} (v : GridVertex 4 n) :
    GridVertex 2 (2 * n) :=
  let upper := v.1.val < 2
  (⟨if v.1.val = 0 ∨ v.1.val = 3 then 0 else 1, by
      split_ifs <;> omega⟩,
    ⟨if upper then v.2.val else n + v.2.val, by
      split_ifs <;> omega⟩)

private def widthFourCombInverse {n : Nat} (v : GridVertex 2 (2 * n)) :
    GridVertex 4 n :=
  (⟨if v.2.val < n then v.1.val else 3 - v.1.val, by
      split_ifs <;> omega⟩,
    ⟨if v.2.val < n then v.2.val else v.2.val - n, by
      split_ifs <;> omega⟩)

private theorem widthFourCombEmbedding_injective {n : Nat} :
    Function.Injective (@widthFourCombEmbedding n) := by
  apply (show Function.LeftInverse (@widthFourCombInverse n)
      (@widthFourCombEmbedding n) by
    intro v
    rcases v with ⟨i, c⟩
    fin_cases i <;>
      apply Prod.ext <;> apply Fin.ext <;>
      simp [widthFourCombInverse, widthFourCombEmbedding]) |>.injective

/-- The forced graph of the two outer rows is acyclic. -/
theorem forced_widthFourOuterRows_isAcyclic {n : Nat} (hn : 2 ≤ n) :
    (forcedEdgeGraph (gridGraph 4 n)
      (↑(widthFourOuterRows n) : Set (GridVertex 4 n))).IsAcyclic := by
  let f : forcedEdgeGraph (gridGraph 4 n)
      (↑(widthFourOuterRows n) : Set (GridVertex 4 n)) →g topSpineColumns 2 (2 * n) :=
    { toFun := widthFourCombEmbedding
      map_rel' := by
        intro v w h
        rcases h with ⟨hgrid, houter⟩
        change adjacent 4 n v w at hgrid
        change v ∈ widthFourOuterRows n ∨ w ∈ widthFourOuterRows n at houter
        rw [mem_widthFourOuterRows, mem_widthFourOuterRows] at houter
        rcases v with ⟨i, c⟩
        rcases w with ⟨j, d⟩
        change topSpineColumnsAdj 2 (2 * n) _ _
        fin_cases i <;> fin_cases j
        all_goals (try simp [adjacent, topSpineColumnsAdj,
          widthFourCombEmbedding] at hgrid houter ⊢)
        all_goals omega }
  have htree := topSpineColumns_two_isTree (N := 2 * n) (by omega)
  exact htree.isAcyclic.comap f widthFourCombEmbedding_injective

/-- A `4 x n` grid preserves at least its two outer rows. -/
theorem two_mul_le_maxPreserved_widthFour {n : Nat} (hn : 2 ≤ n) :
    2 * n ≤ maxPreserved 4 n := by
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  rw [← card_widthFourOuterRows n]
  apply Finset.le_sup (f := Finset.card)
  exact mem_acyclicForcedSets.mpr (forced_widthFourOuterRows_isAcyclic hn)

end GridGraphs
