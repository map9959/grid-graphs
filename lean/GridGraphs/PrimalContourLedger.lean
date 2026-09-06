import GridGraphs.ContourWaste
import GridGraphs.TreeComponentBridge

/-!
# Primal form of the contour ledger

The contour-return term can be eliminated exactly. Its value is the number of
tree edges internal to cotree support plus the number of components induced by
the complementary full vertices, minus one.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

/-- Edges of `G` having both endpoints in `U`, retained on the ambient vertex
type so they can be partitioned directly against forced edges. -/
noncomputable def internalEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ U

@[simp] theorem mem_internalEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (e : Sym2 V) :
    e ∈ internalEdgeFinset G U ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ U := by
  simp [internalEdgeFinset]

/-- Edges incident with the complement of `U` and edges internal to `U`
partition every edge. -/
theorem forced_compl_card_add_internalEdgeFinset_card {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    (forcedEdgeGraph G (↑((Finset.univ : Finset V) \ U) : Set V)).edgeFinset.card +
      (internalEdgeFinset G U).card = G.edgeFinset.card := by
  classical
  let p : Sym2 V → Prop := fun e => ∀ v ∈ e, v ∈ U
  have hforced :
      (forcedEdgeGraph G (↑((Finset.univ : Finset V) \ U) : Set V)).edgeFinset =
        G.edgeFinset.filter fun e => ¬p e := by
    ext e
    induction e using Sym2.inductionOn with
    | _ v w =>
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
        simp [forcedEdgeGraph, p, Sym2.mem_iff]
        tauto
  rw [hforced]
  change (G.edgeFinset.filter fun e => ¬p e).card +
    (G.edgeFinset.filter p).card = G.edgeFinset.card
  simpa [Nat.add_comm] using G.edgeFinset.card_filter_add_card_filter_not p

/-- Outside cotree support, the ambient forced graph agrees with the tree's
forced graph because every incident grid edge is preserved. -/
theorem forced_grid_compl_support_eq_forced_tree
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    let U := supportFinset (gridGraph m n \ T)
    let F := (Finset.univ : Finset (GridVertex m n)) \ U
    forcedEdgeGraph (gridGraph m n) (↑F : Set (GridVertex m n)) =
      forcedEdgeGraph T (↑F : Set (GridVertex m n)) := by
  classical
  dsimp only
  let U := supportFinset (gridGraph m n \ T)
  let F := (Finset.univ : Finset (GridVertex m n)) \ U
  ext v w
  constructor
  · rintro ⟨hgrid, hvF | hwF⟩
    · refine ⟨?_, Or.inl hvF⟩
      have hvU : v ∉ U := (Finset.mem_sdiff.mp hvF).2
      have hpres : preservesIncidentEdges (gridGraph m n) T v := by
        by_contra hnot
        exact hvU ((mem_supportFinset_sdiff_iff_not_preserves
          (gridGraph m n) T hT.le v).2 hnot)
      exact hpres hgrid
    · refine ⟨?_, Or.inr hwF⟩
      have hwU : w ∉ U := (Finset.mem_sdiff.mp hwF).2
      have hpres : preservesIncidentEdges (gridGraph m n) T w := by
        by_contra hnot
        exact hwU ((mem_supportFinset_sdiff_iff_not_preserves
          (gridGraph m n) T hT.le w).2 hnot)
      exact (hpres hgrid.symm).symm
  · rintro ⟨hTree, hF⟩
    exact ⟨hT.le hTree, hF⟩

/-- The ambient forced-forest component count is one plus the number of tree
edges internal to cotree support. -/
theorem card_forced_compl_components_eq_internalTreeEdges_add_one
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    let U := supportFinset (gridGraph m n \ T)
    let F := (Finset.univ : Finset (GridVertex m n)) \ U
    Fintype.card (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).ConnectedComponent =
        (internalEdgeFinset T U).card + 1 := by
  classical
  dsimp only
  let U := supportFinset (gridGraph m n \ T)
  let F := (Finset.univ : Finset (GridVertex m n)) \ U
  have hgraph := forced_grid_compl_support_eq_forced_tree hT
  dsimp only at hgraph
  have hedgeForced :
      (forcedEdgeGraph (gridGraph m n) (↑F : Set (GridVertex m n))).edgeFinset =
        (forcedEdgeGraph T (↑F : Set (GridVertex m n))).edgeFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
    induction e using Sym2.inductionOn with
    | _ v w =>
        exact iff_of_eq (congrFun (congrFun (SimpleGraph.ext_iff.mp hgraph) v) w)
  have hpartition := forced_compl_card_add_internalEdgeFinset_card T U
  have hedgeT := hT.card_edgeFinset
  have hacyc := grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  dsimp only at hacyc
  have hforest := grid_forcedEdgeGraph_forest_ledger m n F hacyc
  change (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).edgeFinset.card +
      Fintype.card (forcedEdgeGraph (gridGraph m n)
        (↑F : Set (GridVertex m n))).ConnectedComponent = m * n at hforest
  rw [hedgeForced] at hforest
  simp only [GridVertex, Fintype.card_prod, Fintype.card_fin] at hedgeT
  have hresource :
      (forcedEdgeGraph T (↑F : Set (GridVertex m n))).edgeFinset.card +
          ((internalEdgeFinset T U).card + 1) = m * n := by
    calc
      _ = ((forcedEdgeGraph T (↑F : Set (GridVertex m n))).edgeFinset.card +
          (internalEdgeFinset T U).card) + 1 := by omega
      _ = T.edgeFinset.card + 1 := by rw [hpartition]
      _ = m * n := hedgeT
  have hcancel := hforest.trans hresource.symm
  have hresult := Nat.add_left_cancel hcancel
  simpa only [U, F] using hresult

/-- Exact primal form of the marked-contour ledger. -/
theorem cotree_incidenceWaste_add_one_eq_boundary_add_internal_add_components
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    incidenceWaste (gridGraph n n \ T) + 1 =
      boundaryDeficiencySum n n U +
        (internalEdgeFinset T U).card +
        Fintype.card ((gridGraph n n).induce
          (↑F : Set (GridVertex n n))).ConnectedComponent := by
  dsimp only
  let U := supportFinset (gridGraph n n \ T)
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  have hbridge := square_grid_tree_component_bridge hn hT
  dsimp only at hbridge
  have hforced := card_forced_compl_components_eq_internalTreeEdges_add_one hT
  dsimp only at hforced
  omega

/-- The weak linear waste bound is exactly a perimeter/internal-edge/component
charge inequality. -/
theorem square_grid_tree_incidenceWaste_ge_side_iff_primalContourCharge
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    n ≤ incidenceWaste (gridGraph n n \ T) ↔
      n + 1 ≤ boundaryDeficiencySum n n U +
        (internalEdgeFinset T U).card +
        Fintype.card ((gridGraph n n).induce
          (↑F : Set (GridVertex n n))).ConnectedComponent := by
  dsimp only
  have hledger :=
    cotree_incidenceWaste_add_one_eq_boundary_add_internal_add_components
      (by omega) hT
  dsimp only at hledger
  omega

end GridGraphs
