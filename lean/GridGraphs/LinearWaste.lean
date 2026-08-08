import GridGraphs.UniversalWaste

/-!
# Linear incidence-waste reduction

This module records unconditional boundary and component consequences of the
forced-forest bridge.  It does not assert the still-open linear component-charge
inequality.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- A vertex lies on one of the four sides of a rectangular grid. -/
def IsGridBoundary {m n : Nat} (v : GridVertex m n) : Prop :=
  v.1.val = 0 ∨ v.1.val + 1 = m ∨ v.2.val = 0 ∨ v.2.val + 1 = n

/-- Every boundary vertex of a nondegenerate grid contributes at least one
unit of ambient degree-four deficiency. -/
lemma one_le_gridBoundaryDeficiency_of_boundary {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (v : GridVertex m n)
    (hv : IsGridBoundary v) : 1 ≤ gridBoundaryDeficiency m n v := by
  unfold IsGridBoundary at hv
  unfold gridBoundaryDeficiency
  by_cases hr : v.1.val = 0 ∨ v.1.val + 1 = m
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = n
    · rw [gridGraph_degree_corner hm hn v hr hc]
      omega
    · rw [gridGraph_degree_border hm hn v (Or.inl ⟨hr, hc⟩)]
  · have hc : v.2.val = 0 ∨ v.2.val + 1 = n := by
      rcases hv with h | h | h | h
      · exact absurd (Or.inl h) hr
      · exact absurd (Or.inr h) hr
      · exact Or.inl h
      · exact Or.inr h
    rw [gridGraph_degree_border hm hn v (Or.inr ⟨hr, hc⟩)]

/-- Two distinct supported boundary vertices contribute at least two units of
boundary deficiency. -/
lemma two_le_boundaryDeficiencySum_of_pair {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (U : Finset (GridVertex m n))
    {v w : GridVertex m n} (hvw : v ≠ w) (hvU : v ∈ U) (hwU : w ∈ U)
    (hv : IsGridBoundary v) (hw : IsGridBoundary w) :
    2 ≤ boundaryDeficiencySum m n U := by
  have hpair : ({v, w} : Finset (GridVertex m n)) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hvU
    · exact hwU
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair
    (fun _ _ _ => Nat.zero_le _) (f := fun x => gridBoundaryDeficiency m n x)
  have hvone := one_le_gridBoundaryDeficiency_of_boundary hm hn v hv
  have hwone := one_le_gridBoundaryDeficiency_of_boundary hm hn w hw
  unfold boundaryDeficiencySum
  simp only [Finset.sum_pair hvw] at hle
  omega

/-- Endpoint deficiency on a path is the sum of its two endpoint indicators.
The hypothesis `2 ≤ n` ensures that the two endpoints are distinct. -/
lemma path_boundary_deficiency_eq_side_indicators {n : Nat} (hn : 2 ≤ n)
    (x : Fin n) :
    2 - (pathGraph n).degree x =
      (if x.val = 0 then 1 else 0) +
        (if x.val + 1 = n then 1 else 0) := by
  by_cases hzero : x.val = 0
  · have hlast : x.val + 1 ≠ n := by omega
    rw [pathGraph_degree_left_end hn x hzero]
    have hone : (1 : Nat) ≠ n := by omega
    simp [hzero, hone]
  · by_cases hlast : x.val + 1 = n
    · rw [pathGraph_degree_right_end hn x hlast]
      simp [hzero, hlast]
    · rw [pathGraph_degree_interior x hzero hlast]
      simp [hzero, hlast]

/-- Grid boundary deficiency splits pointwise into one indicator for each of
the four sides.  Corner vertices consequently contribute to two sides. -/
lemma gridBoundaryDeficiency_eq_four_side_indicators {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (v : GridVertex m n) :
    gridBoundaryDeficiency m n v =
      (if v.1.val = 0 then 1 else 0) +
      (if v.1.val + 1 = m then 1 else 0) +
      (if v.2.val = 0 then 1 else 0) +
      (if v.2.val + 1 = n then 1 else 0) := by
  have hr := path_boundary_deficiency_eq_side_indicators hm v.1
  have hc := path_boundary_deficiency_eq_side_indicators hn v.2
  unfold gridBoundaryDeficiency
  rw [gridGraph_degree]
  have hdr : (pathGraph m).degree v.1 ≤ 2 := by
    by_cases hzero : v.1.val = 0
    · rw [pathGraph_degree_left_end hm v.1 hzero]
      norm_num
    · by_cases hlast : v.1.val + 1 = m
      · rw [pathGraph_degree_right_end hm v.1 hlast]
        norm_num
      · rw [pathGraph_degree_interior v.1 hzero hlast]
  have hdc : (pathGraph n).degree v.2 ≤ 2 := by
    by_cases hzero : v.2.val = 0
    · rw [pathGraph_degree_left_end hn v.2 hzero]
      norm_num
    · by_cases hlast : v.2.val + 1 = n
      · rw [pathGraph_degree_right_end hn v.2 hlast]
        norm_num
      · rw [pathGraph_degree_interior v.2 hzero hlast]
  omega

/-- Exact four-side decomposition of boundary deficiency on an arbitrary grid
vertex set.  The four filters are disjoint except that corners intentionally
occur in the two incident side filters. -/
theorem boundaryDeficiencySum_eq_four_side_card {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (U : Finset (GridVertex m n)) :
    boundaryDeficiencySum m n U =
      (U.filter (fun v => v.1.val = 0)).card +
      (U.filter (fun v => v.1.val + 1 = m)).card +
      (U.filter (fun v => v.2.val = 0)).card +
      (U.filter (fun v => v.2.val + 1 = n)).card := by
  unfold boundaryDeficiencySum
  simp_rw [gridBoundaryDeficiency_eq_four_side_indicators hm hn]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_boole (R := Nat), Finset.sum_boole (R := Nat),
    Finset.sum_boole (R := Nat), Finset.sum_boole (R := Nat)]
  simp

/-- The residual bridge charge written as a four-side component rank.  This
isolates the geometric inequality from the boundary-deficiency encoding. -/
def fourSideComponentRank (n : Nat) (U : Finset (GridVertex n n)) : Nat :=
  (U.filter (fun v => v.1.val = 0)).card +
  (U.filter (fun v => v.1.val + 1 = n)).card +
  (U.filter (fun v => v.2.val = 0)).card +
  (U.filter (fun v => v.2.val + 1 = n)).card +
  Fintype.card ((gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
      Set (GridVertex n n))).ConnectedComponent +
  Fintype.card (forcedEdgeGraph (gridGraph n n)
    (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
      Set (GridVertex n n))).ConnectedComponent

/-- The four-side rank is exactly the boundary/component charge, not merely a
bound on it. -/
theorem fourSideComponentRank_eq_component_charge {n : Nat} (hn : 2 ≤ n)
    (U : Finset (GridVertex n n)) :
    fourSideComponentRank n U =
      boundaryDeficiencySum n n U +
      Fintype.card ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent := by
  rw [boundaryDeficiencySum_eq_four_side_card hn hn]
  rfl

/-- Every square grid tree of side at least three has cotree support carrying
at least two units of boundary deficiency.  Opposite corner cells provide
distinct boundary witnesses. -/
theorem two_le_grid_tree_cotree_boundaryDeficiencySum {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    2 ≤ boundaryDeficiencySum n n (supportFinset (gridGraph n n \ T)) := by
  classical
  let U := supportFinset (gridGraph n n \ T)
  let z : Fin (n - 1) := ⟨0, by omega⟩
  let q : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hnw := grid_tree_cotree_support_hits_cell_edge hT z z
  have hse := grid_tree_cotree_support_hits_cell_edge hT q q
  have hnw' : ∃ v ∈ U, IsGridBoundary v ∧ v.1.val ≤ 1 ∧ v.2.val ≤ 1 := by
    rcases hnw with h | h | h | h
    · exact ⟨cell00 z z, h.1, Or.inl rfl, by simp [cell00, z], by simp [cell00, z]⟩
    · exact ⟨cell01 z z, h.1, Or.inl rfl, by simp [cell01, z], by simp [cell01, z]⟩
    · exact ⟨cell10 z z, h.2, Or.inr (Or.inr (Or.inl rfl)),
        by simp [cell10, z], by simp [cell10, z]⟩
    · exact ⟨cell10 z z, h.1, Or.inr (Or.inr (Or.inl rfl)),
        by simp [cell10, z], by simp [cell10, z]⟩
  have hse' : (∃ v ∈ U, IsGridBoundary v ∧ 1 < v.1.val) ∨
      (∃ v ∈ U, IsGridBoundary v ∧ 1 < v.2.val) := by
    rcases hse with h | h | h | h
    · right
      exact ⟨cell01 q q, h.2, Or.inr (Or.inr (Or.inr (by simp [cell01, q]; omega))),
        by simp [cell01, q]; omega⟩
    · right
      exact ⟨cell11 q q, h.2, Or.inr (Or.inr (Or.inr (by simp [cell11, q]; omega))),
        by simp [cell11, q]; omega⟩
    · left
      exact ⟨cell11 q q, h.1, Or.inr (Or.inl (by simp [cell11, q]; omega)),
        by simp [cell11, q]; omega⟩
    · left
      exact ⟨cell10 q q, h.1, Or.inr (Or.inl (by simp [cell10, q]; omega)),
        by simp [cell10, q]; omega⟩
  obtain ⟨v, hvU, hvb, hvr, hvc⟩ := hnw'
  rcases hse' with ⟨w, hwU, hwb, hwr⟩ | ⟨w, hwU, hwb, hwc⟩
  · apply two_le_boundaryDeficiencySum_of_pair (by omega) (by omega) U
      (fun heq => by
        have heqval : v.1.val = w.1.val := congrArg (fun x => x.1.val) heq
        omega)
      hvU hwU hvb hwb
  · apply two_le_boundaryDeficiencySum_of_pair (by omega) (by omega) U
      (fun heq => by
        have heqval : v.2.val = w.2.val := congrArg (fun x => x.2.val) heq
        omega)
      hvU hwU hvb hwb

/-- A graph on a nonempty finite vertex type has at least one connected
component. -/
lemma one_le_card_connectedComponent {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    1 ≤ Fintype.card G.ConnectedComponent := by
  letI : Nonempty G.ConnectedComponent :=
    Nonempty.map G.connectedComponentMk (inferInstance : Nonempty V)
  exact Fintype.card_pos

/-- Boundary deficiency and the two component types give an unconditional
four-unit floor for the bridge charge. -/
theorem four_le_square_grid_tree_component_charge {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    4 ≤ boundaryDeficiencySum n n U +
      Fintype.card ((gridGraph n n).induce
        (↑F : Set (GridVertex n n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑F : Set (GridVertex n n))).ConnectedComponent := by
  classical
  dsimp only
  let U := supportFinset (gridGraph n n \ T)
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  change 4 ≤ boundaryDeficiencySum n n U +
    Fintype.card ((gridGraph n n).induce
      (↑F : Set (GridVertex n n))).ConnectedComponent +
    Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set (GridVertex n n))).ConnectedComponent
  have hboundary : 2 ≤ boundaryDeficiencySum n n U := by
    simpa only [U] using two_le_grid_tree_cotree_boundaryDeficiencySum hn hT
  let z : GridVertex n n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  letI : Nonempty (GridVertex n n) := ⟨z⟩
  have hambient : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph n n)
        (↑F : Set (GridVertex n n))).ConnectedComponent :=
    one_le_card_connectedComponent _
  by_cases hF : F = ∅
  · have hU : U = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro v
      by_cases hv : v ∈ U
      · exact hv
      · have hvF : v ∈ F := by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
        have hnotF : v ∉ F := by rw [hF]; exact Finset.notMem_empty v
        exact (hnotF hvF).elim
    have htotal := total_boundaryDeficiencySum (m := n) (n := n)
      (by omega) (by omega)
    rw [hU] at hboundary ⊢
    omega
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨v, hv⟩ := hFne
    letI : Nonempty (↑F : Set (GridVertex n n)) := ⟨⟨v, hv⟩⟩
    have hinduced : 1 ≤ Fintype.card
        ((gridGraph n n).induce
          (↑F : Set (GridVertex n n))).ConnectedComponent :=
      one_le_card_connectedComponent _
    omega

/-- The boundary-component method alone already proves the constant lower
bound `W ≥ 2`; obtaining growth in `n` requires the residual charge inequality
below. -/
theorem two_le_square_grid_tree_incidenceWaste {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    2 ≤ incidenceWaste (gridGraph n n \ T) := by
  have hcharge := four_le_square_grid_tree_component_charge hn hT
  have hbridge := square_grid_tree_component_bridge (by omega) hT
  omega

/-- The tree bridge makes `W ≥ n` exactly the following boundary-component
charge inequality. -/
theorem square_grid_tree_incidenceWaste_ge_side_iff_component_charge {n : Nat}
    (hn : 3 ≤ n) {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    n ≤ incidenceWaste (gridGraph n n \ T) ↔
      n + 2 ≤ boundaryDeficiencySum n n U +
        Fintype.card ((gridGraph n n).induce (↑F : Set (GridVertex n n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph n n)
          (↑F : Set (GridVertex n n))).ConnectedComponent := by
  dsimp only
  have hbridge := square_grid_tree_component_bridge (by omega) hT
  omega

/-- Four-side form of the remaining linear rank inequality.  All boundary
geometry is now exposed as four side-intersection cardinalities; the only
other terms are the two forest component counts. -/
theorem square_grid_tree_incidenceWaste_ge_side_iff_fourSideComponentRank
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    n ≤ incidenceWaste (gridGraph n n \ T) ↔
      n + 2 ≤ fourSideComponentRank n U := by
  dsimp only
  let U := supportFinset (gridGraph n n \ T)
  have hcharge := square_grid_tree_incidenceWaste_ge_side_iff_component_charge
    hn hT
  dsimp only at hcharge
  have hrank := fourSideComponentRank_eq_component_charge (by omega) U
  change n ≤ incidenceWaste (gridGraph n n \ T) ↔
    n + 2 ≤ fourSideComponentRank n U
  rw [hcharge, hrank]

/-- For reference, the stronger universal target `W ≥ n+2` differs only by
two units in the exact residual component charge. -/
theorem square_grid_tree_universalWaste_iff_component_charge {n : Nat}
    (hn : 3 ≤ n) {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) ↔
      n + 4 ≤ boundaryDeficiencySum n n U +
        Fintype.card ((gridGraph n n).induce (↑F : Set (GridVertex n n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph n n)
          (↑F : Set (GridVertex n n))).ConnectedComponent := by
  dsimp only
  have hbridge := square_grid_tree_component_bridge (by omega) hT
  omega

end GridGraphs
