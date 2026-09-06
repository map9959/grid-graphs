import GridGraphs.Accounting.ComponentReduction
import GridGraphs.Forests.LabelledComponentQuotient
import GridGraphs.Surgery.ThreeFrameSurgery

/-!
# Cycle defect of a contracted star bundle

When a vertex `u` is inserted into a forced set, the new edges form a star
from `u` to the neighbors not already forced.  This file contracts the current
forced graph, while retaining the star-edge labels, and records the resulting
graphic defect.  The defect counts loops and repetitions among component
labels; no acyclicity hypothesis is needed for the counting statements.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

/-- Neighbors whose edge to `u` is newly owned by the insertion of `u`. -/
noncomputable def starAttachmentLeaves [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Finset V := by
  classical
  exact (G.neighborFinset u).filter fun v => v ∉ F

@[simp] theorem mem_starAttachmentLeaves [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u v : V) :
    v ∈ starAttachmentLeaves G F u ↔ G.Adj u v ∧ v ∉ F := by
  classical
  simp [starAttachmentLeaves]

/-- Component label of a vertex in the current forced graph. -/
def forcedComponentLabel (G : SimpleGraph V) (F : Set V) (v : V) :
    (forcedEdgeGraph G F).ConnectedComponent :=
  (forcedEdgeGraph G F).connectedComponentMk v

/-- The multiset of contracted leaf labels.  Multiplicity is retained. -/
noncomputable def contractedStarAttachmentMultiset [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    Multiset (forcedEdgeGraph G F).ConnectedComponent :=
  (starAttachmentLeaves G F u).val.map (forcedComponentLabel G F)

/-- Number of leaves carrying one fixed contracted component label. -/
noncomputable def starAttachmentMultiplicity [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V)
    (c : (forcedEdgeGraph G F).ConnectedComponent) : Nat := by
  classical
  exact ((starAttachmentLeaves G F u).filter fun v =>
    forcedComponentLabel G F v = c).card

/-- Occupied component labels, with multiplicity forgotten. -/
noncomputable def starAttachmentComponents [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    Finset (forcedEdgeGraph G F).ConnectedComponent := by
  classical
  exact (starAttachmentLeaves G F u).image (forcedComponentLabel G F)

/-- Occupied leaf components other than the central component. -/
noncomputable def noncentralStarAttachmentComponents [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    Finset (forcedEdgeGraph G F).ConnectedComponent := by
  classical
  exact (starAttachmentComponents G F u).erase (forcedComponentLabel G F u)

/-- Distinct noncentral component labels reached by the star.  This is the
graphic rank of the contracted star bundle. -/
noncomputable def starAttachmentGraphicRank [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Nat := by
  exact (noncentralStarAttachmentComponents G F u).card

/-- Independent cycle defect of the contracted star: edge count minus graphic
rank. -/
noncomputable def bundleCycleDefect [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Nat :=
  (starAttachmentLeaves G F u).card - starAttachmentGraphicRank G F u

/-- Label-retaining quotient bundle for the new star edges. -/
noncomputable def contractedStarLabelledQuotientBundle [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    SimpleGraph (SimpleGraph.LabelledExtensionVertex
      (forcedEdgeGraph G F).ConnectedComponent V) :=
  SimpleGraph.labelledComponentQuotient (forcedEdgeGraph G F)
    (fun v => (u, v)) (starAttachmentLeaves G F u)

private theorem attachment_fiber_sum [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    (starAttachmentLeaves G F u).card =
      ∑ c ∈ starAttachmentComponents G F u,
        starAttachmentMultiplicity G F u c := by
  classical
  unfold starAttachmentComponents
  exact Finset.card_eq_sum_card_fiberwise
    (f := forcedComponentLabel G F)
    (t := (starAttachmentLeaves G F u).image (forcedComponentLabel G F))
    (by intro v hv; exact Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Exact loop-plus-repetition formula.  The first term is the number of
contracted loops at the central component.  Every other occupied component
contributes its multiplicity minus one. -/
theorem bundleCycleDefect_eq_loop_add_repetitions [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    bundleCycleDefect G F u =
      starAttachmentMultiplicity G F u (forcedComponentLabel G F u) +
        ∑ c ∈ noncentralStarAttachmentComponents G F u,
          (starAttachmentMultiplicity G F u c - 1) := by
  classical
  let S := starAttachmentLeaves G F u
  let f := forcedComponentLabel G F
  let center := f u
  let I := starAttachmentComponents G F u
  let J := noncentralStarAttachmentComponents G F u
  have hI : I = S.image f := rfl
  have hJ : J = I.erase center := rfl
  have hsum : S.card = ∑ c ∈ I, starAttachmentMultiplicity G F u c := by
    exact attachment_fiber_sum G F u
  have hpositive : ∀ c ∈ I, 1 ≤ starAttachmentMultiplicity G F u c := by
    intro c hc
    obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp (hI ▸ hc)
    apply Finset.card_pos.mpr
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvc⟩⟩
  have hsplit :
      (∑ c ∈ I, starAttachmentMultiplicity G F u c) =
        starAttachmentMultiplicity G F u center +
          ∑ c ∈ J, starAttachmentMultiplicity G F u c := by
    by_cases hc : center ∈ I
    · have h := Finset.sum_erase_add I (starAttachmentMultiplicity G F u) hc
      rw [hJ]
      omega
    · have hzero : starAttachmentMultiplicity G F u center = 0 := by
        simp only [starAttachmentMultiplicity, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro v hv heq
        exact hc (hI.symm ▸ Finset.mem_image.mpr ⟨v, hv, heq⟩)
      have hJI : J = I := hJ.trans (Finset.erase_eq_of_notMem hc)
      simp [hJI, hzero]
  have hrepetitions :
      (∑ c ∈ J, starAttachmentMultiplicity G F u c) =
        J.card + ∑ c ∈ J, (starAttachmentMultiplicity G F u c - 1) := by
    rw [Finset.card_eq_sum_ones]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hcI : c ∈ I := Finset.mem_of_mem_erase hc
    have hp := hpositive c hcI
    omega
  change S.card - J.card =
    starAttachmentMultiplicity G F u center +
      ∑ c ∈ J, (starAttachmentMultiplicity G F u c - 1)
  rw [hsum, hsplit, hrepetitions]
  omega

/-- The graphic-rank ledger for the bundle extension. -/
theorem bundleCycleDefect_add_graphicRank [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    bundleCycleDefect G F u + starAttachmentGraphicRank G F u =
      (starAttachmentLeaves G F u).card := by
  classical
  unfold bundleCycleDefect
  have hle : starAttachmentGraphicRank G F u ≤
      (starAttachmentLeaves G F u).card := by
    unfold starAttachmentGraphicRank noncentralStarAttachmentComponents
    unfold starAttachmentComponents
    exact (Finset.card_erase_le.trans Finset.card_image_le)
  omega

private def IndependentStarAttachmentLabels [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Prop :=
  forcedComponentLabel G F u ∉
      starAttachmentComponents G F u ∧
    Set.InjOn (forcedComponentLabel G F) (starAttachmentLeaves G F u)

private theorem independentStarAttachmentLabels_iff [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    IndependentStarAttachmentLabels G F u ↔ ForcedInsertionCondition G F u := by
  classical
  constructor
  · rintro ⟨hcenter, hinj⟩ v hv w hw hvw hreach
    have heq := SimpleGraph.ConnectedComponent.sound hreach
    rcases hv with hv | hv
    · subst v
      rcases hw with hw | hw
      · exact hvw hw.symm
      · apply hcenter
        unfold starAttachmentComponents
        exact Finset.mem_image.mpr
          ⟨w, (mem_starAttachmentLeaves G F u w).mpr hw, heq.symm⟩
    · rcases hw with hw | hw
      · subst w
        apply hcenter
        unfold starAttachmentComponents
        exact Finset.mem_image.mpr
          ⟨v, (mem_starAttachmentLeaves G F u v).mpr hv, heq⟩
      · apply hvw
        apply hinj ((mem_starAttachmentLeaves G F u v).mpr hv)
          ((mem_starAttachmentLeaves G F u w).mpr hw)
        exact heq
  · intro h
    constructor
    · rintro hc
      unfold starAttachmentComponents at hc
      obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp hc
      have huv : u ≠ v := fun huv => (mem_starAttachmentLeaves G F u v).mp hv |>.1.ne huv
      exact h (v := u) (by simp) (w := v)
        (by exact Or.inr ((mem_starAttachmentLeaves G F u v).mp hv)) huv
        (SimpleGraph.ConnectedComponent.exact hvc.symm)
    · intro v hv w hw heq
      by_contra hvw
      exact h (v := v) (Or.inr ((mem_starAttachmentLeaves G F u v).mp hv))
        (w := w) (Or.inr ((mem_starAttachmentLeaves G F u w).mp hw)) hvw
        (SimpleGraph.ConnectedComponent.exact heq)

/-- Vanishing cycle defect is exactly the one-vertex forced insertion
condition. -/
theorem bundleCycleDefect_eq_zero_iff_forcedInsertionCondition [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    bundleCycleDefect G F u = 0 ↔ ForcedInsertionCondition G F u := by
  classical
  rw [← independentStarAttachmentLabels_iff]
  let S := starAttachmentLeaves G F u
  let f := forcedComponentLabel G F
  let center := f u
  let I := starAttachmentComponents G F u
  have hIdef : I = S.image f := rfl
  constructor
  · intro hzero
    have hrank : S.card ≤ (I.erase center).card := by
      simpa [bundleCycleDefect, starAttachmentGraphicRank,
        noncentralStarAttachmentComponents, S, f, center, I,
        Nat.sub_eq_zero_iff_le] using hzero
    have herase_le : (I.erase center).card ≤ I.card := Finset.card_erase_le
    have himage_le : I.card ≤ S.card := by
      rw [hIdef]
      exact Finset.card_image_le
    have hIE : (I.erase center).card = I.card := by
      omega
    have hcenter : center ∉ I := by
      intro hc
      have hpos : 0 < I.card := Finset.card_pos.mpr ⟨center, hc⟩
      have herase := Finset.card_erase_of_mem hc
      rw [herase] at hIE
      omega
    refine ⟨hcenter, (Finset.card_image_iff.mp ?_)⟩
    have hI : I.card = S.card := by omega
    simpa [hIdef] using hI
  · rintro ⟨hcenter, hinj⟩
    have hI : I.card = S.card := by
      rw [hIdef]
      exact Finset.card_image_iff.mpr hinj
    have herase : I.erase center = I := Finset.erase_eq_of_notMem hcenter
    have hnoncentral : noncentralStarAttachmentComponents G F u = I := by
      change I.erase center = I
      exact herase
    change S.card - (noncentralStarAttachmentComponents G F u).card = 0
    rw [hnoncentral, hI]
    exact Nat.sub_self _

/-- Every vertex omitted from a one-vertex-maximal forced-acyclic set has
positive bundle-cycle defect. -/
theorem bundleCycleDefect_pos_of_maximalForcedAcyclic [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Set V) (hmax : MaximalForcedAcyclic G F) {u : V} (hu : u ∉ F) :
    1 ≤ bundleCycleDefect G F u := by
  by_contra hpos
  have hzero : bundleCycleDefect G F u = 0 := by omega
  have hinsertion : ForcedInsertionCondition G F u :=
    (bundleCycleDefect_eq_zero_iff_forcedInsertionCondition G F u).mp hzero
  have hacyclic : (forcedEdgeGraph G (insert u F)).IsAcyclic :=
    (forcedEdgeGraph_insert_isAcyclic_iff hu hmax.1).mpr hinsertion
  exact hmax.2 u hu hacyclic

/-- Summing the preceding pointwise obstruction over the omitted vertices. -/
theorem card_compl_le_sum_bundleCycleDefect_of_maximalForcedAcyclic
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset V)
    (hmax : MaximalForcedAcyclic G (↑F : Set V)) :
    (Finset.univ \ F).card ≤
      ∑ u ∈ Finset.univ \ F,
        bundleCycleDefect G (↑F : Set V) u := by
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro u hu
  exact bundleCycleDefect_pos_of_maximalForcedAcyclic G (↑F : Set V) hmax
    (by simpa using (Finset.mem_sdiff.mp hu).2)

/-- If neither the owner nor any of its neighbors is forced, the owner is
isolated in the current forced graph, so no star edge contracts to a loop. -/
theorem forcedComponentLabel_ne_of_no_forced_neighbor [Fintype V]
    (G : SimpleGraph V) (F : Set V) {u v : V} (hu : u ∉ F)
    (hneighbor : ∀ x, G.Adj u x → x ∉ F)
    (hv : v ∈ starAttachmentLeaves G F u) :
    forcedComponentLabel G F v ≠ forcedComponentLabel G F u := by
  intro heq
  have hreach := SimpleGraph.ConnectedComponent.exact heq
  have hisolated : ∀ x, ¬(forcedEdgeGraph G F).Adj u x := by
    intro x hx
    exact hx.2.elim hu (hneighbor x hx.1)
  have huv : u ≠ v := ((mem_starAttachmentLeaves G F u v).mp hv).1.ne
  have hsupport := SimpleGraph.mem_support_of_reachable huv hreach.symm
  obtain ⟨x, hux⟩ := (SimpleGraph.mem_support _).mp hsupport
  exact hisolated x hux

/-- Defect never exceeds the number of star edges. -/
theorem bundleCycleDefect_le_attachment_card [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) :
    bundleCycleDefect G F u ≤ (starAttachmentLeaves G F u).card := by
  exact Nat.sub_le _ _

/-- The star edge count is bounded by ambient degree. -/
theorem starAttachmentLeaves_card_le_degree [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) [DecidableRel G.Adj] :
    (starAttachmentLeaves G F u).card ≤ G.degree u := by
  classical
  apply Finset.card_le_card
  intro v hv
  simpa only [SimpleGraph.mem_neighborFinset] using
    (mem_starAttachmentLeaves G F u v).mp hv |>.1

/-- Grid degree and boundary deficiency give a four-unit defect budget. -/
theorem bundleCycleDefect_add_gridBoundaryDeficiency_le_four
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n) :
    bundleCycleDefect (gridGraph m n) F u + gridBoundaryDeficiency m n u ≤ 4 := by
  have hdef := bundleCycleDefect_le_attachment_card (gridGraph m n) F u
  have hcard := starAttachmentLeaves_card_le_degree (gridGraph m n) F u
  unfold gridBoundaryDeficiency
  have hdegree := gridGraph_degree_le_four m n u
  omega

/-- For a genuine next repair candidate, the independent cycle defect is at
most three.  If there are no new edges it is zero; otherwise one unit of the
degree-four budget is graphic rank. -/
theorem bundleCycleDefect_le_three_of_not_forced
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n) (hu : u ∉ F) :
    bundleCycleDefect (gridGraph m n) F u ≤ 3 := by
  classical
  by_contra hthree
  have hdef := bundleCycleDefect_le_attachment_card (gridGraph m n) F u
  have hcard := starAttachmentLeaves_card_le_degree (gridGraph m n) F u
  have hdegree := gridGraph_degree_le_four m n u
  have hfour : bundleCycleDefect (gridGraph m n) F u = 4 := by omega
  have hledger := bundleCycleDefect_add_graphicRank (gridGraph m n) F u
  have hrank : starAttachmentGraphicRank (gridGraph m n) F u = 0 := by omega
  have hleafcard : (starAttachmentLeaves (gridGraph m n) F u).card = 4 := by omega
  have hdegreefour : (gridGraph m n).degree u = 4 := by omega
  have heq : starAttachmentLeaves (gridGraph m n) F u =
      (gridGraph m n).neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simpa only [SimpleGraph.mem_neighborFinset] using
        (mem_starAttachmentLeaves (gridGraph m n) F u v).mp hv |>.1
    · rw [show ((gridGraph m n).neighborFinset u).card = 4 from hdegreefour,
        hleafcard]
  have hnonempty : (starAttachmentLeaves (gridGraph m n) F u).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hnonempty
  have hneighbor : ∀ x, (gridGraph m n).Adj u x → x ∉ F := by
    intro x hx
    exact (mem_starAttachmentLeaves (gridGraph m n) F u x).mp
      (by rw [heq]; simpa only [SimpleGraph.mem_neighborFinset] using hx) |>.2
  have hne := forcedComponentLabel_ne_of_no_forced_neighbor
    (gridGraph m n) F hu hneighbor hv
  have hmem : forcedComponentLabel (gridGraph m n) F v ∈
      noncentralStarAttachmentComponents (gridGraph m n) F u := by
    unfold noncentralStarAttachmentComponents starAttachmentComponents
    exact Finset.mem_erase.mpr
      ⟨hne, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have : 1 ≤ starAttachmentGraphicRank (gridGraph m n) F u := by
    unfold starAttachmentGraphicRank
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- Defect four is possible only outside the next-candidate hypotheses.  It
uses all four incident edges, has rank zero, lies at boundary deficiency zero,
and its owner is already forced.  The last fact is the forced-overlap resource
that a neighboring-crop argument would have to account for. -/
theorem bundleCycleDefect_eq_four_geometry
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n)
    (hfour : bundleCycleDefect (gridGraph m n) F u = 4) :
    u ∈ F ∧
      (starAttachmentLeaves (gridGraph m n) F u).card = 4 ∧
      starAttachmentGraphicRank (gridGraph m n) F u = 0 ∧
      (gridGraph m n).degree u = 4 ∧
      gridBoundaryDeficiency m n u = 0 := by
  classical
  have hu : u ∈ F := by
    by_contra hu
    have := bundleCycleDefect_le_three_of_not_forced F u hu
    omega
  have hledger := bundleCycleDefect_add_graphicRank (gridGraph m n) F u
  have hcard := starAttachmentLeaves_card_le_degree (gridGraph m n) F u
  have hdegree := gridGraph_degree_le_four m n u
  have hbudget := bundleCycleDefect_add_gridBoundaryDeficiency_le_four F u
  refine ⟨hu, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Under defect four every grid neighbor is an attachment leaf: there is no
unused incident edge and no neighboring forced vertex. -/
theorem starAttachmentLeaves_eq_neighborFinset_of_defect_eq_four
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n)
    (hfour : bundleCycleDefect (gridGraph m n) F u = 4) :
    starAttachmentLeaves (gridGraph m n) F u = (gridGraph m n).neighborFinset u := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simpa only [SimpleGraph.mem_neighborFinset] using
      (mem_starAttachmentLeaves (gridGraph m n) F u v).mp hv |>.1
  · have hgeometry := bundleCycleDefect_eq_four_geometry F u hfour
    change (gridGraph m n).degree u ≤
      (starAttachmentLeaves (gridGraph m n) F u).card
    omega

/-- Exact exceptional-case characterization.  Thus defect four can occur for
an arbitrary current forced set, but only when the proposed owner is already
forced, is degree four, and has no forced neighbor.  A genuine next candidate
excludes precisely the first hypothesis. -/
theorem bundleCycleDefect_eq_four_iff
    {m n : Nat} (F : Set (GridVertex m n)) (u : GridVertex m n) :
    bundleCycleDefect (gridGraph m n) F u = 4 ↔
      u ∈ F ∧ (gridGraph m n).degree u = 4 ∧
        ∀ v, (gridGraph m n).Adj u v → v ∉ F := by
  classical
  constructor
  · intro hfour
    have hgeometry := bundleCycleDefect_eq_four_geometry F u hfour
    have hleaves := starAttachmentLeaves_eq_neighborFinset_of_defect_eq_four F u hfour
    refine ⟨hgeometry.1, hgeometry.2.2.2.1, ?_⟩
    intro v huv
    have hv : v ∈ starAttachmentLeaves (gridGraph m n) F u := by
      rw [hleaves]
      simpa only [SimpleGraph.mem_neighborFinset] using huv
    exact (mem_starAttachmentLeaves (gridGraph m n) F u v).mp hv |>.2
  · rintro ⟨hu, hdegree, hneighbor⟩
    have hleaves : starAttachmentLeaves (gridGraph m n) F u =
        (gridGraph m n).neighborFinset u := by
      ext v
      simp only [mem_starAttachmentLeaves, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.1, fun h => ⟨h, hneighbor v h⟩⟩
    have hlabels : starAttachmentComponents (gridGraph m n) F u =
        {forcedComponentLabel (gridGraph m n) F u} := by
      ext c
      constructor
      · intro hc
        unfold starAttachmentComponents at hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
        apply Finset.mem_singleton.mpr
        apply SimpleGraph.ConnectedComponent.sound
        apply SimpleGraph.Adj.reachable
        exact ⟨(mem_starAttachmentLeaves (gridGraph m n) F u v).mp hv |>.1.symm,
          Or.inr hu⟩
      · intro hc
        have hnonempty : (starAttachmentLeaves (gridGraph m n) F u).Nonempty := by
          rw [hleaves]
          apply Finset.card_pos.mp
          change 0 < (gridGraph m n).degree u
          omega
        obtain ⟨v, hv⟩ := hnonempty
        have hlabel : forcedComponentLabel (gridGraph m n) F v =
            forcedComponentLabel (gridGraph m n) F u := by
          apply SimpleGraph.ConnectedComponent.sound
          apply SimpleGraph.Adj.reachable
          exact ⟨(mem_starAttachmentLeaves (gridGraph m n) F u v).mp hv |>.1.symm,
            Or.inr hu⟩
        unfold starAttachmentComponents
        rw [Finset.mem_singleton.mp hc]
        exact Finset.mem_image.mpr ⟨v, hv, hlabel⟩
    have hrank : starAttachmentGraphicRank (gridGraph m n) F u = 0 := by
      unfold starAttachmentGraphicRank noncentralStarAttachmentComponents
      rw [hlabels]
      simp
    have hcard : (starAttachmentLeaves (gridGraph m n) F u).card = 4 := by
      rw [hleaves]
      exact hdegree
    unfold bundleCycleDefect
    rw [hcard, hrank]

/-- In a nondegenerate rectangle, the exceptional value four is geometrically
interior. -/
theorem interior_of_bundleCycleDefect_eq_four
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) (F : Set (GridVertex m n))
    (u : GridVertex m n)
    (hfour : bundleCycleDefect (gridGraph m n) F u = 4) :
    ¬(u.1.val = 0 ∨ u.1.val + 1 = m) ∧
      ¬(u.2.val = 0 ∨ u.2.val + 1 = n) := by
  have hdegree := (bundleCycleDefect_eq_four_geometry F u hfour).2.2.2.1
  constructor
  · intro hrow
    by_cases hcol : u.2.val = 0 ∨ u.2.val + 1 = n
    · have := gridGraph_degree_corner hm hn u hrow hcol
      omega
    · have := gridGraph_degree_border hm hn u (Or.inl ⟨hrow, hcol⟩)
      omega
  · intro hcol
    by_cases hrow : u.1.val = 0 ∨ u.1.val + 1 = m
    · have := gridGraph_degree_corner hm hn u hrow hcol
      omega
    · have := gridGraph_degree_border hm hn u (Or.inr ⟨hrow, hcol⟩)
      omega

end GridGraphs
