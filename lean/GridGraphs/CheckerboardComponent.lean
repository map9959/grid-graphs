import GridGraphs.ComponentReduction

/-!
# Checkerboard component reduction

The square-grid upper bound can be studied through two symmetric forests.  For
an acyclic forced-edge graph on a vertex set `F`, one forest contains the full
black stars and every white vertex; the other contains the full white stars and
every black vertex.  Their component counts replace the two less symmetric
component counts in `grid_component_reduction`.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The even checkerboard class of grid vertices. -/
def gridBlack (m n : Nat) : Finset (GridVertex m n) :=
  Finset.univ.filter fun v => (v.1.val + v.2.val) % 2 = 0

/-- The odd checkerboard class, defined as the complement of `gridBlack`. -/
def gridWhite (m n : Nat) : Finset (GridVertex m n) :=
  Finset.univ \ gridBlack m n

/-- Grid adjacency swaps checkerboard classes. -/
lemma grid_adj_mem_black_iff_not_mem_black {m n : Nat}
    {v w : GridVertex m n} (hvw : (gridGraph m n).Adj v w) :
    v ∈ gridBlack m n ↔ w ∉ gridBlack m n := by
  unfold gridGraph adjacent at hvw
  unfold gridBlack
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hvw with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · have hval : v.1.val = w.1.val := congrArg Fin.val hrow
    rcases hcol with h | h <;> omega
  · have hval : v.2.val = w.2.val := congrArg Fin.val hcol
    rcases hrow with h | h <;> omega

/-- The checkerboard classes form a bipartition of the grid graph. -/
theorem gridGraph_isBipartiteWith_checkerboard (m n : Nat) :
    (gridGraph m n).IsBipartiteWith
      (↑(gridBlack m n) : Set (GridVertex m n))
      (↑(gridWhite m n) : Set (GridVertex m n)) := by
  constructor
  · rw [Set.disjoint_left]
    intro v hvB hvW
    change v ∈ gridBlack m n at hvB
    change v ∈ gridWhite m n at hvW
    exact (Finset.mem_sdiff.mp hvW).2 hvB
  · intro v w hvw
    have hswap := grid_adj_mem_black_iff_not_mem_black hvw
    by_cases hv : v ∈ gridBlack m n
    · left
      exact ⟨hv, by
        change w ∈ gridWhite m n
        simpa [gridWhite] using hswap.mp hv⟩
    · right
      have hw : w ∈ gridBlack m n := by
        by_contra hnw
        exact hv (hswap.mpr hnw)
      exact ⟨by
        change v ∈ gridWhite m n
        simpa [gridWhite] using hv, hw⟩

/-- Full black centers retained in the black-star forest. -/
def blackCenters {m n : Nat} (F : Finset (GridVertex m n)) :
    Finset (GridVertex m n) :=
  F ∩ gridBlack m n

/-- Full white centers retained in the white-star forest. -/
def whiteCenters {m n : Nat} (F : Finset (GridVertex m n)) :
    Finset (GridVertex m n) :=
  F ∩ gridWhite m n

/-- Vertex set of the forest made of full black stars. -/
def blackStarVertices {m n : Nat} (F : Finset (GridVertex m n)) :
    Finset (GridVertex m n) :=
  blackCenters F ∪ gridWhite m n

/-- Vertex set of the forest made of full white stars. -/
def whiteStarVertices {m n : Nat} (F : Finset (GridVertex m n)) :
    Finset (GridVertex m n) :=
  whiteCenters F ∪ gridBlack m n

/-- The forest made of all ambient edges in the full-black-star vertex set. -/
def blackStarGraph {m n : Nat} (F : Finset (GridVertex m n)) :
    SimpleGraph (↑(blackStarVertices F) : Set (GridVertex m n)) :=
  (gridGraph m n).induce (↑(blackStarVertices F) : Set (GridVertex m n))

/-- The forest made of all ambient edges in the full-white-star vertex set. -/
def whiteStarGraph {m n : Nat} (F : Finset (GridVertex m n)) :
    SimpleGraph (↑(whiteStarVertices F) : Set (GridVertex m n)) :=
  (gridGraph m n).induce (↑(whiteStarVertices F) : Set (GridVertex m n))

instance blackStarGraph_decidableRel {m n : Nat}
    (F : Finset (GridVertex m n)) : DecidableRel (blackStarGraph F).Adj := by
  unfold blackStarGraph
  infer_instance

instance whiteStarGraph_decidableRel {m n : Nat}
    (F : Finset (GridVertex m n)) : DecidableRel (whiteStarGraph F).Adj := by
  unfold whiteStarGraph
  infer_instance

/-- The checkerboard classes partition all grid vertices. -/
lemma gridBlack_union_gridWhite (m n : Nat) :
    gridBlack m n ∪ gridWhite m n = Finset.univ := by
  unfold gridWhite
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-- The full vertices partition into their black and white centers. -/
lemma blackCenters_union_whiteCenters {m n : Nat}
    (F : Finset (GridVertex m n)) :
    blackCenters F ∪ whiteCenters F = F := by
  unfold blackCenters whiteCenters
  rw [← Finset.inter_union_distrib_left, gridBlack_union_gridWhite]
  simp

private lemma blackStar_edge_has_center {m n : Nat}
    (F : Finset (GridVertex m n)) {v w : GridVertex m n}
    (hvw : (gridGraph m n).Adj v w)
    (hv : v ∈ blackStarVertices F) (hw : w ∈ blackStarVertices F) :
    v ∈ blackCenters F ∨ w ∈ blackCenters F := by
  rcases (gridGraph_isBipartiteWith_checkerboard m n).mem_of_adj hvw with
    ⟨hvB, hwW⟩ | ⟨hvW, hwB⟩
  · left
    rcases Finset.mem_union.mp hv with hvC | hvW'
    · exact hvC
    · exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
        ⟨hvB, hvW'⟩).elim
  · right
    rcases Finset.mem_union.mp hw with hwC | hwW'
    · exact hwC
    · exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
        ⟨hwB, hwW'⟩).elim

private lemma whiteStar_edge_has_center {m n : Nat}
    (F : Finset (GridVertex m n)) {v w : GridVertex m n}
    (hvw : (gridGraph m n).Adj v w)
    (hv : v ∈ whiteStarVertices F) (hw : w ∈ whiteStarVertices F) :
    v ∈ whiteCenters F ∨ w ∈ whiteCenters F := by
  rcases (gridGraph_isBipartiteWith_checkerboard m n).mem_of_adj hvw with
    ⟨hvB, hwW⟩ | ⟨hvW, hwB⟩
  · right
    rcases Finset.mem_union.mp hw with hwC | hwB'
    · exact hwC
    · exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
        ⟨hwB', hwW⟩).elim
  · left
    rcases Finset.mem_union.mp hv with hvC | hvB'
    · exact hvC
    · exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
        ⟨hvB', hvW⟩).elim

/-- On the black-star vertices, forcing the black centers retains every ambient
edge. -/
lemma blackStarGraph_eq_forced_induce {m n : Nat}
    (F : Finset (GridVertex m n)) :
    blackStarGraph F =
      (forcedEdgeGraph (gridGraph m n)
        (↑(blackCenters F) : Set (GridVertex m n))).induce
          (↑(blackStarVertices F) : Set (GridVertex m n)) := by
  ext v w
  change (gridGraph m n).Adj v.1 w.1 ↔
    (gridGraph m n).Adj v.1 w.1 ∧
      (v.1 ∈ blackCenters F ∨ w.1 ∈ blackCenters F)
  exact ⟨fun h => ⟨h, blackStar_edge_has_center F h v.property w.property⟩,
    fun h => h.1⟩

/-- White analogue of `blackStarGraph_eq_forced_induce`. -/
lemma whiteStarGraph_eq_forced_induce {m n : Nat}
    (F : Finset (GridVertex m n)) :
    whiteStarGraph F =
      (forcedEdgeGraph (gridGraph m n)
        (↑(whiteCenters F) : Set (GridVertex m n))).induce
          (↑(whiteStarVertices F) : Set (GridVertex m n)) := by
  ext v w
  change (gridGraph m n).Adj v.1 w.1 ↔
    (gridGraph m n).Adj v.1 w.1 ∧
      (v.1 ∈ whiteCenters F ∨ w.1 ∈ whiteCenters F)
  exact ⟨fun h => ⟨h, whiteStar_edge_has_center F h v.property w.property⟩,
    fun h => h.1⟩

private lemma forced_blackCenters_isAcyclic {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    (forcedEdgeGraph (gridGraph m n)
      (↑(blackCenters F) : Set (GridVertex m n))).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti _ hH
  intro v w hvw
  exact ⟨hvw.1, hvw.2.imp
    (fun hv => (Finset.mem_inter.mp hv).1)
    (fun hw => (Finset.mem_inter.mp hw).1)⟩

private lemma forced_whiteCenters_isAcyclic {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    (forcedEdgeGraph (gridGraph m n)
      (↑(whiteCenters F) : Set (GridVertex m n))).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti _ hH
  intro v w hvw
  exact ⟨hvw.1, hvw.2.imp
    (fun hv => (Finset.mem_inter.mp hv).1)
    (fun hw => (Finset.mem_inter.mp hw).1)⟩

/-- Acyclicity of the full forced graph implies acyclicity of the black-star
graph. -/
lemma blackStarGraph_isAcyclic {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    (blackStarGraph F).IsAcyclic := by
  rw [blackStarGraph_eq_forced_induce]
  exact (forced_blackCenters_isAcyclic F hH).induce _

/-- Acyclicity of the full forced graph implies acyclicity of the white-star
graph. -/
lemma whiteStarGraph_isAcyclic {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    (whiteStarGraph F).IsAcyclic := by
  rw [whiteStarGraph_eq_forced_induce]
  exact (forced_whiteCenters_isAcyclic F hH).induce _

private lemma gridGraph_induce_blackCenters_eq_bot {m n : Nat}
    (F : Finset (GridVertex m n)) :
    (gridGraph m n).induce
      (↑(blackCenters F) : Set (GridVertex m n)) = ⊥ := by
  ext v w
  change (gridGraph m n).Adj v.1 w.1 ↔ False
  rw [iff_false]
  intro hvw
  have hvB := (Finset.mem_inter.mp v.property).2
  have hwB := (Finset.mem_inter.mp w.property).2
  have hwW := (gridGraph_isBipartiteWith_checkerboard m n).mem_of_mem_adj hvB hvw
  exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
    ⟨hwB, hwW⟩).elim

private lemma gridGraph_induce_whiteCenters_eq_bot {m n : Nat}
    (F : Finset (GridVertex m n)) :
    (gridGraph m n).induce
      (↑(whiteCenters F) : Set (GridVertex m n)) = ⊥ := by
  ext v w
  change (gridGraph m n).Adj v.1 w.1 ↔ False
  rw [iff_false]
  intro hvw
  have hvW := (Finset.mem_inter.mp v.property).2
  have hwW := (Finset.mem_inter.mp w.property).2
  have hwB := (gridGraph_isBipartiteWith_checkerboard m n).symm.mem_of_mem_adj hvW hvw
  exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
    ⟨hwB, hwW⟩).elim

private lemma forced_blackCenters_support_subset {m n : Nat}
    (F : Finset (GridVertex m n)) :
    (forcedEdgeGraph (gridGraph m n)
      (↑(blackCenters F) : Set (GridVertex m n))).support ⊆
        (↑(blackStarVertices F) : Set (GridVertex m n)) := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  rcases hvw.2 with hvC | hwC
  · exact Finset.mem_union_left _ hvC
  · apply Finset.mem_union_right
    have hwB := (Finset.mem_inter.mp hwC).2
    exact (gridGraph_isBipartiteWith_checkerboard m n).symm.mem_of_mem_adj'
      hwB hvw.1

private lemma forced_whiteCenters_support_subset {m n : Nat}
    (F : Finset (GridVertex m n)) :
    (forcedEdgeGraph (gridGraph m n)
      (↑(whiteCenters F) : Set (GridVertex m n))).support ⊆
        (↑(whiteStarVertices F) : Set (GridVertex m n)) := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  rcases hvw.2 with hvC | hwC
  · exact Finset.mem_union_left _ hvC
  · apply Finset.mem_union_right
    have hwW := (Finset.mem_inter.mp hwC).2
    exact (gridGraph_isBipartiteWith_checkerboard m n).mem_of_mem_adj'
      hwW hvw.1

/-- The two center sets are disjoint. -/
lemma blackCenters_disjoint_whiteCenters {m n : Nat}
    (F : Finset (GridVertex m n)) :
    Disjoint (blackCenters F) (whiteCenters F) := by
  rw [Finset.disjoint_left]
  intro v hvB hvW
  have hvBlack := (Finset.mem_inter.mp hvB).2
  have hvWhite := (Finset.mem_inter.mp hvW).2
  exact ((gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
    ⟨hvBlack, hvWhite⟩).elim

/-- Degree sums over the two checkerboard center sets partition the degree sum
over all full vertices. -/
lemma sum_degrees_blackCenters_add_whiteCenters {m n : Nat}
    (F : Finset (GridVertex m n)) :
    (∑ v ∈ blackCenters F, (gridGraph m n).degree v) +
        (∑ v ∈ whiteCenters F, (gridGraph m n).degree v) =
      ∑ v ∈ F, (gridGraph m n).degree v := by
  rw [← Finset.sum_union (blackCenters_disjoint_whiteCenters F),
    blackCenters_union_whiteCenters]

/-- Boundary deficiency partitions exactly between the two checkerboard center
sets.  In particular, a forced corner remains charged twice in the sum. -/
lemma boundaryDeficiencySum_blackCenters_add_whiteCenters {m n : Nat}
    (F : Finset (GridVertex m n)) :
    boundaryDeficiencySum m n (blackCenters F) +
        boundaryDeficiencySum m n (whiteCenters F) =
      boundaryDeficiencySum m n F := by
  unfold boundaryDeficiencySum
  rw [← Finset.sum_union (blackCenters_disjoint_whiteCenters F),
    blackCenters_union_whiteCenters]

/-- Exact black-center component formula.  Since black centers are independent,
their forced-edge count is their ambient degree sum. -/
theorem black_center_component_ledger {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    4 * (blackCenters F).card +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑(blackCenters F) : Set (GridVertex m n))).ConnectedComponent =
      m * n + boundaryDeficiencySum m n (blackCenters F) := by
  have hledger := grid_forcedEdgeGraph_forest_ledger m n (blackCenters F)
    (forced_blackCenters_isAcyclic F hH)
  have hrestricted := sum_degrees_finset_eq_forced_add_induced
    (gridGraph m n) (blackCenters F)
  have hzero : ((gridGraph m n).induce
      (↑(blackCenters F) : Set (GridVertex m n))).edgeFinset.card = 0 := by
    simp [gridGraph_induce_blackCenters_eq_bot]
  have hdef := sum_degrees_add_boundaryDeficiencySum m n (blackCenters F)
  omega

/-- White analogue of `black_center_component_ledger`. -/
theorem white_center_component_ledger {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    4 * (whiteCenters F).card +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑(whiteCenters F) : Set (GridVertex m n))).ConnectedComponent =
      m * n + boundaryDeficiencySum m n (whiteCenters F) := by
  have hledger := grid_forcedEdgeGraph_forest_ledger m n (whiteCenters F)
    (forced_whiteCenters_isAcyclic F hH)
  have hrestricted := sum_degrees_finset_eq_forced_add_induced
    (gridGraph m n) (whiteCenters F)
  have hzero : ((gridGraph m n).induce
      (↑(whiteCenters F) : Set (GridVertex m n))).edgeFinset.card = 0 := by
    simp [gridGraph_induce_whiteCenters_eq_bot]
  have hdef := sum_degrees_add_boundaryDeficiencySum m n (whiteCenters F)
  omega

/-- Exact checkerboard component identity on the ambient grid.  Vertices not
belonging to a given star forest are retained as isolated components; this
ambient normalization avoids subtraction in `Nat`. -/
theorem grid_checkerboard_ambient_component_reduction {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    4 * F.card +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑(blackCenters F) : Set (GridVertex m n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑(whiteCenters F) : Set (GridVertex m n))).ConnectedComponent =
      2 * (m * n) + boundaryDeficiencySum m n F := by
  classical
  have hblackAcyc := forced_blackCenters_isAcyclic F hH
  have hwhiteAcyc := forced_whiteCenters_isAcyclic F hH
  have hblack := grid_forcedEdgeGraph_forest_ledger m n (blackCenters F) hblackAcyc
  have hwhite := grid_forcedEdgeGraph_forest_ledger m n (whiteCenters F) hwhiteAcyc
  have hblackRestricted := sum_degrees_finset_eq_forced_add_induced
    (gridGraph m n) (blackCenters F)
  have hwhiteRestricted := sum_degrees_finset_eq_forced_add_induced
    (gridGraph m n) (whiteCenters F)
  have hblackZero : ((gridGraph m n).induce
      (↑(blackCenters F) : Set (GridVertex m n))).edgeFinset.card = 0 := by
    simp [gridGraph_induce_blackCenters_eq_bot]
  have hwhiteZero : ((gridGraph m n).induce
      (↑(whiteCenters F) : Set (GridVertex m n))).edgeFinset.card = 0 := by
    simp [gridGraph_induce_whiteCenters_eq_bot]
  have hdegreePartition := sum_degrees_blackCenters_add_whiteCenters F
  have hdef := sum_degrees_add_boundaryDeficiencySum m n F
  omega

/-- The ambient checkerboard component sum is the original two-component
charge plus one isolated-component credit for every vertex outside `F`. -/
theorem checkerboard_component_sum_eq_component_charge_add_compl
    {m n : Nat} (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    Fintype.card (forcedEdgeGraph (gridGraph m n)
        (↑(blackCenters F) : Set (GridVertex m n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph m n)
        (↑(whiteCenters F) : Set (GridVertex m n))).ConnectedComponent =
      (Finset.univ \ F).card +
        Fintype.card ((gridGraph m n).induce
          (↑F : Set (GridVertex m n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑F : Set (GridVertex m n))).ConnectedComponent := by
  have hchecker := grid_checkerboard_ambient_component_reduction F hH
  have hold := grid_component_reduction F hH
  have hcard := card_compl_add_card_grid m n F
  omega

end GridGraphs
