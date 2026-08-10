import GridGraphs.CheckerboardComponent
import GridGraphs.BundleToothCut

/-!
# Triangle-free grid insertion

The checkerboard bipartition excludes triangles in every grid graph.  Combined
with the bundle tooth deletion, this gives a three-vertex de-forcing budget for
inserting any genuine new forced owner while preserving acyclicity.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Every rectangular grid graph is triangle-free. -/
theorem gridGraph_cliqueFree_three (m n : Nat) :
    (gridGraph m n).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ :=
    SimpleGraph.is3Clique_iff.mp hs
  have hab' := grid_adj_mem_black_iff_not_mem_black hab
  have hac' := grid_adj_mem_black_iff_not_mem_black hac
  have hbc' := grid_adj_mem_black_iff_not_mem_black hbc
  by_cases ha : a ∈ gridBlack m n
  · have hb : b ∉ gridBlack m n := hab'.mp ha
    have hc : c ∉ gridBlack m n := hac'.mp ha
    exact hb (hbc'.mpr hc)
  · have hb : b ∈ gridBlack m n := by
      by_contra hb
      exact ha (hab'.mpr hb)
    have hc : c ∉ gridBlack m n := hbc'.mp hb
    exact ha (hac'.mpr hc)

/-- In a grid, a genuine new forced owner can be inserted acyclically after
de-forcing at most three forced vertices, none adjacent to the new owner. -/
theorem exists_grid_deletion_for_forcedEdgeGraph_insert_isAcyclic
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n)
    (hu : u ∉ F) (hF : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    ∃ D : Finset (GridVertex m n),
      (↑D : Set (GridVertex m n)) ⊆ F ∧
      Disjoint (↑D : Set (GridVertex m n)) ((gridGraph m n).neighborSet u) ∧
      D.card ≤ 3 ∧
      (forcedEdgeGraph (gridGraph m n)
        (insert u (F \ (↑D : Set (GridVertex m n))))).IsAcyclic := by
  obtain ⟨D, hDF, hDN, hcard, hacyclic⟩ :=
    exists_deletion_for_forcedEdgeGraph_insert_isAcyclic
      (gridGraph m n) (gridGraph_cliqueFree_three m n) F u hu hF
  exact ⟨D, hDF, hDN,
    hcard.trans (bundleCycleDefect_le_three_of_not_forced F u hu), hacyclic⟩

end GridGraphs
