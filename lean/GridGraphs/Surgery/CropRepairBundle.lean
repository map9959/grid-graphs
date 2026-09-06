import GridGraphs.Surgery.ThreeFrameSurgery
import GridGraphs.Geometry.GridEdge
import GridGraphs.Forests.LabelledComponentQuotient

/-!
# Physical edge bundles for crop repair

A repair vertex forces all of its incident grid edges.  Edges already forced by
the cropped set are omitted here, so the remaining labels describe exactly the
new part of the forced graph.  Labels are `GridEdge`s rather than
vertex-edge incidences: when two repair vertices are adjacent, their bundles
overlap in the same physical edge.

The final theorem combines the exact physical graph equality with subdivision
and the labelled component contraction theorem.  Thus admissibility is
characterized by the label-retaining quotient forest, including loops and
parallel quotient fibers.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

variable {B : Type*}

/-- A coordinate edge is incident to a vertex when the vertex is one of its
two physical endpoints. -/
def GridEdge.Incident {m n : Nat} (edge : GridEdge m n)
    (v : GridVertex m n) : Prop :=
  edge.primalEndpoints.1 = v ∨ edge.primalEndpoints.2 = v

/-- The physical edges newly activated by a crop repair.  The endpoint tests
remove every edge already present in the initial cropped forced graph. -/
def physicalCropRepairEdges {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) : Finset (GridEdge m n) :=
  Finset.univ.filter fun edge =>
    (edge.primalEndpoints.1 ∈ R ∨ edge.primalEndpoints.2 ∈ R) ∧
      edge.primalEndpoints.1 ∉ cropForcedSet e F ∧
      edge.primalEndpoints.2 ∉ cropForcedSet e F

@[simp] theorem mem_physicalCropRepairEdges {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (edge : GridEdge m n) :
    edge ∈ physicalCropRepairEdges e F R ↔
      (edge.primalEndpoints.1 ∈ R ∨ edge.primalEndpoints.2 ∈ R) ∧
        edge.primalEndpoints.1 ∉ cropForcedSet e F ∧
        edge.primalEndpoints.2 ∉ cropForcedSet e F := by
  simp [physicalCropRepairEdges]

/-- The part of the physical repair edge set contributed by one repair
vertex.  Bundles intentionally overlap. -/
def cropRepairBundle {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (u : GridVertex m n) :
    Finset (GridEdge m n) :=
  (physicalCropRepairEdges e F R).filter fun edge =>
    edge.primalEndpoints.1 = u ∨ edge.primalEndpoints.2 = u

@[simp] theorem mem_cropRepairBundle {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (u : GridVertex m n)
    (edge : GridEdge m n) :
    edge ∈ cropRepairBundle e F R u ↔
      edge ∈ physicalCropRepairEdges e F R ∧ edge.Incident u := by
  simp [cropRepairBundle, GridEdge.Incident]

/-- Every new physical edge is covered by the bundle of one of its repair
endpoints. -/
theorem mem_physicalCropRepairEdges_iff_exists_bundle {m n : Nat}
    [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (edge : GridEdge m n) :
    edge ∈ physicalCropRepairEdges e F R ↔
      ∃ u ∈ R, edge ∈ cropRepairBundle e F R u := by
  constructor
  · intro hedge
    rcases (mem_physicalCropRepairEdges e F R edge).mp hedge |>.1 with hu | hu
    · exact ⟨edge.primalEndpoints.1, hu, by simp [hedge, GridEdge.Incident]⟩
    · exact ⟨edge.primalEndpoints.2, hu, by simp [hedge, GridEdge.Incident]⟩
  · rintro ⟨u, -, hu⟩
    exact (mem_cropRepairBundle e F R u edge).mp hu |>.1

/-- Membership in two bundles means that the one physical edge is incident to
both bundle vertices. -/
theorem mem_two_cropRepairBundles_iff {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (u v : GridVertex m n)
    (edge : GridEdge m n) :
    edge ∈ cropRepairBundle e F R u ∩ cropRepairBundle e F R v ↔
      edge ∈ physicalCropRepairEdges e F R ∧
        edge.Incident u ∧ edge.Incident v := by
  constructor
  · intro h
    have hu := (mem_cropRepairBundle e F R u edge).mp
      (Finset.mem_inter.mp h).1
    have hv := (mem_cropRepairBundle e F R v edge).mp
      (Finset.mem_inter.mp h).2
    exact ⟨hu.1, hu.2, hv.2⟩
  · rintro ⟨hedge, hu, hv⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_cropRepairBundle e F R u edge).mpr ⟨hedge, hu⟩,
        (mem_cropRepairBundle e F R v edge).mpr ⟨hedge, hv⟩⟩

/-- Distinct bundle vertices can overlap only on the physical edge joining
them.  In particular there cannot be two copies of that edge. -/
theorem primalSym2_eq_of_mem_two_cropRepairBundles {m n : Nat}
    [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) {u v : GridVertex m n} (huv : u ≠ v)
    {edge : GridEdge m n}
    (hedge : edge ∈ cropRepairBundle e F R u ∩ cropRepairBundle e F R v) :
    edge.primalSym2 = s(u, v) := by
  have h := (mem_two_cropRepairBundles_iff e F R u v edge).mp hedge
  rcases h.2.1 with hxu | hyu <;> rcases h.2.2 with hxv | hyv
  · exact (huv (hxu.symm.trans hxv)).elim
  · simp [GridEdge.primalSym2, hxu, hyv]
  · rw [GridEdge.primalSym2, hyu, hxv]
    exact Sym2.eq_swap
  · exact (huv (hyu.symm.trans hyv)).elim

/-- The simple graph represented by a finite set of physical coordinate
edges. -/
def physicalGridEdgeGraph {m n : Nat} (S : Finset (GridEdge m n)) :
    SimpleGraph (GridVertex m n) :=
  SimpleGraph.fromEdgeSet (GridEdge.primalSym2 '' (↑S : Set (GridEdge m n)))

theorem physicalGridEdgeGraph_adj_iff {m n : Nat}
    (S : Finset (GridEdge m n)) (u v : GridVertex m n) :
    (physicalGridEdgeGraph S).Adj u v ↔
      ∃ edge ∈ S, edge.primalSym2 = s(u, v) := by
  constructor
  · intro h
    rw [physicalGridEdgeGraph, SimpleGraph.fromEdgeSet_adj] at h
    rcases h.1 with ⟨edge, hedge, heq⟩
    exact ⟨edge, hedge, heq⟩
  · rintro ⟨edge, hedge, heq⟩
    rw [physicalGridEdgeGraph, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨edge, hedge, heq⟩, ?_⟩
    intro huv
    subst v
    have hloop : (gridGraph m n).Adj u u := by
      rw [← SimpleGraph.mem_edgeSet, ← heq]
      exact GridEdge.primalSym2_mem_gridGraph_edgeSet edge
    exact (gridGraph m n).loopless.irrefl u hloop

private theorem physicalGridEdgeGraph_edgeSet {m n : Nat}
    (S : Finset (GridEdge m n)) :
    (physicalGridEdgeGraph S).edgeSet =
      GridEdge.primalSym2 '' (↑S : Set (GridEdge m n)) := by
  rw [physicalGridEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  rw [sdiff_eq_left]
  apply Set.disjoint_left.mpr
  rintro _ ⟨edge, -, rfl⟩ hdiag
  have hadj := GridEdge.primalSym2_mem_gridGraph_edgeSet edge
  exact (gridGraph m n).not_isDiag_of_mem_edgeSet hadj hdiag

private lemma adj_finset_sup_exists {E W : Type*} (P : E → SimpleGraph W)
    (S : Finset E) {x y : W} (h : (S.sup P).Adj x y) :
    ∃ edge ∈ S, (P edge).Adj x y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at h
  | @insert edge S hedge ih =>
      rw [sup_insert, sup_adj] at h
      rcases h with h | h
      · exact ⟨edge, mem_insert_self edge S, h⟩
      · obtain ⟨other, hother, h⟩ := ih h
        exact ⟨other, mem_insert_of_mem hother, h⟩

/-- Collapse the two private subdivision vertices of a physical edge onto its
two endpoints. -/
private def collapseGridEdgeVertex {m n : Nat} :
    SimpleGraph.LabelledExtensionVertex (GridVertex m n) (GridEdge m n) →
      GridVertex m n
  | Sum.inl v => v
  | Sum.inr (edge, false) => edge.primalEndpoints.1
  | Sum.inr (edge, true) => edge.primalEndpoints.2

private lemma collapseGridEdgeVertex_adj {m n : Nat}
    (H : SimpleGraph (GridVertex m n)) (S : Finset (GridEdge m n))
    {x y : SimpleGraph.LabelledExtensionVertex
      (GridVertex m n) (GridEdge m n)}
    (hxy : (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj x y) :
    collapseGridEdgeVertex x = collapseGridEdgeVertex y ∨
      (H ⊔ physicalGridEdgeGraph S).Adj
        (collapseGridEdgeVertex x) (collapseGridEdgeVertex y) := by
  classical
  rw [SimpleGraph.labelledExtension, sup_adj] at hxy
  rcases hxy with hbase | hpath
  · rcases hbase with ⟨_, u, v, huv, rfl, rfl⟩
    exact Or.inr (Or.inl huv)
  · obtain ⟨edge, hedge, hpath⟩ := adj_finset_sup_exists
      (SimpleGraph.labelledPath GridEdge.primalEndpoints) S hpath
    simp only [SimpleGraph.labelledPath, sup_adj, SimpleGraph.fromEdgeSet_adj,
      Set.mem_singleton_iff, Sym2.eq_iff] at hpath
    rcases hpath with (hpath | hpath) | hpath
    · rcases hpath.1 with h | h <;> rcases h with ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
    · rcases hpath.1 with h | h <;> rcases h with ⟨rfl, rfl⟩
      · right
        right
        exact (physicalGridEdgeGraph_adj_iff S _ _).mpr
          ⟨edge, hedge, rfl⟩
      · right
        right
        apply (physicalGridEdgeGraph_adj_iff S _ _).mpr
        exact ⟨edge, hedge, Sym2.eq_swap⟩
    · rcases hpath.1 with h | h <;> rcases h with ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl

private lemma labelledExtension_endpoints_reachable {m n : Nat}
    (H : SimpleGraph (GridVertex m n)) (S : Finset (GridEdge m n))
    {edge : GridEdge m n} (hedge : edge ∈ S) :
    (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Reachable
      (Sum.inl edge.primalEndpoints.1) (Sum.inl edge.primalEndpoints.2) := by
  have h₁ : (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj
      (Sum.inl edge.primalEndpoints.1) (Sum.inr (edge, false)) := by
    rw [SimpleGraph.labelledExtension, sup_adj]
    right
    apply (Finset.le_sup hedge :
      SimpleGraph.labelledPath GridEdge.primalEndpoints edge ≤ _)
    simp [SimpleGraph.labelledPath]
  have h₂ : (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj
      (Sum.inr (edge, false)) (Sum.inr (edge, true)) := by
    rw [SimpleGraph.labelledExtension, sup_adj]
    right
    apply (Finset.le_sup hedge :
      SimpleGraph.labelledPath GridEdge.primalEndpoints edge ≤ _)
    simp [SimpleGraph.labelledPath]
  have h₃ : (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj
      (Sum.inr (edge, true)) (Sum.inl edge.primalEndpoints.2) := by
    rw [SimpleGraph.labelledExtension, sup_adj]
    right
    apply (Finset.le_sup hedge :
      SimpleGraph.labelledPath GridEdge.primalEndpoints edge ≤ _)
    simp [SimpleGraph.labelledPath]
  exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)

/-- Subdivision preserves reachability between original grid vertices. -/
private theorem physicalExtension_reachable_iff_labelledExtension {m n : Nat}
    (H : SimpleGraph (GridVertex m n)) (S : Finset (GridEdge m n))
    (u v : GridVertex m n) :
    (H ⊔ physicalGridEdgeGraph S).Reachable u v ↔
      (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Reachable
        (Sum.inl u) (Sum.inl v) := by
  constructor
  · intro huv
    rw [reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => exact Reachable.refl _
    | @tail w v huw hwv ih =>
        apply ih.trans
        rcases hwv with hwv | hwv
        · exact (show (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj
              (Sum.inl w) (Sum.inl v) from
                Or.inl ⟨Sum.inl_injective.ne hwv.ne, w, v, hwv, rfl, rfl⟩).reachable
        · obtain ⟨edge, hedge, heq⟩ :=
            (physicalGridEdgeGraph_adj_iff S w v).mp hwv
          rw [GridEdge.primalSym2, Sym2.eq_iff] at heq
          rcases heq with ⟨hw, hv⟩ | ⟨hw, hv⟩
          · simpa only [hw, hv] using labelledExtension_endpoints_reachable H S hedge
          · exact (by simpa only [hw, hv] using
              (labelledExtension_endpoints_reachable H S hedge).symm)
  · intro huv
    rw [reachable_iff_reflTransGen] at huv
    have hcollapse : ∀ {x y}, Relation.ReflTransGen
        (SimpleGraph.labelledExtension H GridEdge.primalEndpoints S).Adj x y →
        (H ⊔ physicalGridEdgeGraph S).Reachable
          (collapseGridEdgeVertex x) (collapseGridEdgeVertex y) := by
      intro x y h
      induction h with
      | refl => exact Reachable.refl _
      | tail hxy hyz ih =>
          rcases collapseGridEdgeVertex_adj H S hyz with heq | hadj
          · simpa only [heq] using ih
          · exact ih.trans hadj.reachable
    simpa [collapseGridEdgeVertex] using hcollapse huv

/-- Exact decomposition of the repaired forced graph into the initial forced
graph and the graph represented by the new physical edges. -/
theorem forcedEdgeGraph_crop_union_repair_eq {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (_hR : IsCropRepairSet e F R) :
    forcedEdgeGraph (gridGraph m n)
        (↑(cropForcedSet e F ∪ R) : Set (GridVertex m n)) =
      forcedEdgeGraph (gridGraph m n)
          (↑(cropForcedSet e F) : Set (GridVertex m n)) ⊔
        physicalGridEdgeGraph (physicalCropRepairEdges e F R) := by
  ext u v
  simp only [forcedEdgeGraph, sup_adj, physicalGridEdgeGraph_adj_iff]
  constructor
  · rintro ⟨huv, hforced⟩
    have hforced' :
        (u ∈ cropForcedSet e F ∨ u ∈ R) ∨
          (v ∈ cropForcedSet e F ∨ v ∈ R) := by
      simpa only [Finset.mem_coe, Finset.mem_union] using hforced
    rcases hforced' with (hu | hu) | (hv | hv)
    · exact Or.inl ⟨huv, Or.inl hu⟩
    · by_cases huC : u ∈ cropForcedSet e F
      · exact Or.inl ⟨huv, Or.inl huC⟩
      by_cases hvC : v ∈ cropForcedSet e F
      · exact Or.inl ⟨huv, Or.inr hvC⟩
      · right
        let edge := (GridEdge.equivGridGraphEdgeSet m n).symm
          ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩
        have hedgeSym : edge.primalSym2 = s(u, v) := by
          exact congrArg Subtype.val
            ((GridEdge.equivGridGraphEdgeSet m n).apply_symm_apply
              ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩)
        have hends :
            (edge.primalEndpoints.1 = u ∧ edge.primalEndpoints.2 = v) ∨
              (edge.primalEndpoints.1 = v ∧ edge.primalEndpoints.2 = u) := by
          rw [GridEdge.primalSym2, Sym2.eq_iff] at hedgeSym
          rcases hedgeSym with h | h
          · exact Or.inl h
          · exact Or.inr h
        refine ⟨edge, ?_, hedgeSym⟩
        rw [mem_physicalCropRepairEdges]
        rcases hends with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
        · exact ⟨Or.inl (by simpa only [hxu] using hu),
            by simpa only [hxu] using huC, by simpa only [hyv] using hvC⟩
        · exact ⟨Or.inr (by simpa only [hyu] using hu),
            by simpa only [hxv] using hvC, by simpa only [hyu] using huC⟩
    · exact Or.inl ⟨huv, Or.inr hv⟩
    · by_cases huC : u ∈ cropForcedSet e F
      · exact Or.inl ⟨huv, Or.inl huC⟩
      by_cases hvC : v ∈ cropForcedSet e F
      · exact Or.inl ⟨huv, Or.inr hvC⟩
      · right
        let edge := (GridEdge.equivGridGraphEdgeSet m n).symm
          ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩
        have hedgeSym : edge.primalSym2 = s(u, v) := by
          exact congrArg Subtype.val
            ((GridEdge.equivGridGraphEdgeSet m n).apply_symm_apply
              ⟨s(u, v), by simpa [SimpleGraph.mem_edgeSet] using huv⟩)
        have hends :
            (edge.primalEndpoints.1 = u ∧ edge.primalEndpoints.2 = v) ∨
              (edge.primalEndpoints.1 = v ∧ edge.primalEndpoints.2 = u) := by
          rw [GridEdge.primalSym2, Sym2.eq_iff] at hedgeSym
          rcases hedgeSym with h | h
          · exact Or.inl h
          · exact Or.inr h
        refine ⟨edge, ?_, hedgeSym⟩
        rw [mem_physicalCropRepairEdges]
        rcases hends with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
        · exact ⟨Or.inr (by simpa only [hyv] using hv),
            by simpa only [hxu] using huC, by simpa only [hyv] using hvC⟩
        · exact ⟨Or.inl (by simpa only [hxv] using hv),
            by simpa only [hxv] using hvC, by simpa only [hyu] using huC⟩
  · rintro (hinitial | ⟨edge, hedge, hedgeSym⟩)
    · refine ⟨hinitial.1, ?_⟩
      rcases hinitial.2 with hu | hv
      · left
        exact Finset.mem_union.mpr (Or.inl hu)
      · right
        exact Finset.mem_union.mpr (Or.inl hv)
    · have hphysical := (mem_physicalCropRepairEdges e F R edge).mp hedge
      have hgrid : (gridGraph m n).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        rw [← hedgeSym]
        exact GridEdge.primalSym2_mem_gridGraph_edgeSet edge
      have hends :
          (edge.primalEndpoints.1 = u ∧ edge.primalEndpoints.2 = v) ∨
            (edge.primalEndpoints.1 = v ∧ edge.primalEndpoints.2 = u) := by
        rw [GridEdge.primalSym2, Sym2.eq_iff] at hedgeSym
        rcases hedgeSym with h | h
        · exact Or.inl h
        · exact Or.inr h
      refine ⟨hgrid, ?_⟩
      rcases hends with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · rcases hphysical.1 with hu | hv
        · left
          exact Finset.mem_union.mpr
            (Or.inr (by simpa only [hxu] using hu))
        · right
          exact Finset.mem_union.mpr
            (Or.inr (by simpa only [hyv] using hv))
      · rcases hphysical.1 with hv | hu
        · right
          exact Finset.mem_union.mpr
            (Or.inr (by simpa only [hxv] using hv))
        · left
          exact Finset.mem_union.mpr
            (Or.inr (by simpa only [hyu] using hu))

/-- Initial forced graph used when contracting a crop repair. -/
def cropInitialForcedGraph {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B) :
    SimpleGraph (GridVertex m n) :=
  forcedEdgeGraph (gridGraph m n) (↑(cropForcedSet e F) : Set (GridVertex m n))

private theorem physicalCropRepairEdge_not_initial {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) {edge : GridEdge m n}
    (hedge : edge ∈ physicalCropRepairEdges e F R) :
    ¬(cropInitialForcedGraph e F).Adj
      edge.primalEndpoints.1 edge.primalEndpoints.2 := by
  intro h
  have hout := (mem_physicalCropRepairEdges e F R edge).mp hedge
  exact h.2.elim hout.2.1 hout.2.2

private theorem physicalCropExtension_delete {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) {edge : GridEdge m n}
    (hedge : edge ∈ physicalCropRepairEdges e F R) :
    ((cropInitialForcedGraph e F ⊔
        physicalGridEdgeGraph (physicalCropRepairEdges e F R)) \
      SimpleGraph.fromEdgeSet {edge.primalSym2}) =
      cropInitialForcedGraph e F ⊔
        physicalGridEdgeGraph ((physicalCropRepairEdges e F R).erase edge) := by
  apply SimpleGraph.edgeSet_injective
  rw [SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_fromEdgeSet,
    SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup,
    physicalGridEdgeGraph_edgeSet, physicalGridEdgeGraph_edgeSet]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_image, Finset.mem_coe, Finset.mem_erase]
  constructor
  · rintro ⟨hxH | ⟨other, hother, rfl⟩, hxne⟩
    · exact Or.inl hxH
    · right
      refine ⟨other, ⟨?_, hother⟩, rfl⟩
      intro heq
      subst other
      apply hxne
      exact ⟨rfl, (gridGraph m n).not_isDiag_of_mem_edgeSet
        (GridEdge.primalSym2_mem_gridGraph_edgeSet edge)⟩
  · rintro (hxH | ⟨other, ⟨hne, hother⟩, rfl⟩)
    · refine ⟨Or.inl hxH, ?_⟩
      rintro ⟨heq, -⟩
      apply physicalCropRepairEdge_not_initial e F R hedge
      rw [← SimpleGraph.mem_edgeSet]
      simpa only [heq, GridEdge.primalSym2] using hxH
    · refine ⟨Or.inr ⟨other, hother, rfl⟩, ?_⟩
      rintro ⟨heq, -⟩
      exact hne (GridEdge.primalSym2_injective heq)

/-- Acyclicity of the physical extension has the same erase-one-label test as
the subdivided labelled extension. -/
private theorem physicalCropExtension_isAcyclic_iff_erased {m n : Nat}
    [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n))
    (hcrop : (cropInitialForcedGraph e F).IsAcyclic) :
    (cropInitialForcedGraph e F ⊔
        physicalGridEdgeGraph (physicalCropRepairEdges e F R)).IsAcyclic ↔
      ∀ edge ∈ physicalCropRepairEdges e F R,
        ¬(cropInitialForcedGraph e F ⊔
            physicalGridEdgeGraph
              ((physicalCropRepairEdges e F R).erase edge)).Reachable
          edge.primalEndpoints.1 edge.primalEndpoints.2 := by
  classical
  let H := cropInitialForcedGraph e F
  let S := physicalCropRepairEdges e F R
  constructor
  · intro hAll edge hedge hreach
    have hadj : (H ⊔ physicalGridEdgeGraph S).Adj
        edge.primalEndpoints.1 edge.primalEndpoints.2 := by
      right
      exact (physicalGridEdgeGraph_adj_iff S _ _).mpr ⟨edge, hedge, rfl⟩
    have hdelete := physicalCropExtension_delete e F R hedge
    obtain ⟨x, c, hc, -⟩ :=
      (adj_and_reachable_delete_edges_iff_exists_cycle
        (G := H ⊔ physicalGridEdgeGraph S)
        (v := edge.primalEndpoints.1) (w := edge.primalEndpoints.2)).mp
          ⟨hadj, by
            change (((cropInitialForcedGraph e F ⊔
              physicalGridEdgeGraph (physicalCropRepairEdges e F R)) \
                SimpleGraph.fromEdgeSet {edge.primalSym2}).Reachable
                  edge.primalEndpoints.1 edge.primalEndpoints.2)
            rw [physicalCropExtension_delete e F R hedge]
            exact hreach⟩
    exact hAll c hc
  · intro herased x c hc
    by_cases hbase : ∀ edge ∈ c.edges, edge ∈ H.edgeSet
    · exact hcrop (c.transfer H hbase) (hc.transfer hbase)
    · push Not at hbase
      obtain ⟨physical, hphysicalCycle, hphysicalBase⟩ := hbase
      have hphysicalAll := c.edges_subset_edgeSet hphysicalCycle
      rw [SimpleGraph.edgeSet_sup, physicalGridEdgeGraph_edgeSet] at hphysicalAll
      rcases hphysicalAll with hphysicalH | ⟨edge, hedge, hedgeEq⟩
      · exact (hphysicalBase hphysicalH).elim
      · have hedgeCycle : edge.primalSym2 ∈ c.edges := by
          simpa only [hedgeEq] using hphysicalCycle
        have hcycleData :=
          (adj_and_reachable_delete_edges_iff_exists_cycle
            (G := H ⊔ physicalGridEdgeGraph S)
            (v := edge.primalEndpoints.1) (w := edge.primalEndpoints.2)).mpr
              ⟨x, c, hc, hedgeCycle⟩
        apply herased edge hedge
        rw [← physicalCropExtension_delete e F R hedge]
        exact hcycleData.2

/-- Replacing every physical repair edge by its private three-edge labelled
path preserves acyclicity. -/
private theorem physicalCropExtension_isAcyclic_iff_labelledExtension
    {m n : Nat} [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n))
    (hcrop : (cropInitialForcedGraph e F).IsAcyclic) :
    (cropInitialForcedGraph e F ⊔
        physicalGridEdgeGraph (physicalCropRepairEdges e F R)).IsAcyclic ↔
      (SimpleGraph.labelledExtension (cropInitialForcedGraph e F)
        GridEdge.primalEndpoints (physicalCropRepairEdges e F R)).IsAcyclic := by
  classical
  let H := cropInitialForcedGraph e F
  let S := physicalCropRepairEdges e F R
  rw [physicalCropExtension_isAcyclic_iff_erased e F R hcrop]
  rw [SimpleGraph.labelledExtension_isAcyclic_iff_componentQuotient H hcrop]
  rw [SimpleGraph.labelledComponentQuotient_isAcyclic_iff]
  constructor
  · intro herased edge hedge
    refine ⟨?_, ?_⟩
    · intro hsame
      apply herased edge hedge
      exact (SimpleGraph.ConnectedComponent.exact hsame).mono
        (fun _ _ hadj => Or.inl hadj)
    · intro hquotient
      apply herased edge hedge
      apply (physicalExtension_reachable_iff_labelledExtension H
        (S.erase edge) _ _).mpr
      apply (SimpleGraph.labelledExtension_reachable_iff_componentQuotient
        H GridEdge.primalEndpoints (S.erase edge)
          (Sum.inl edge.primalEndpoints.1)
          (Sum.inl edge.primalEndpoints.2)).mpr
      exact hquotient
  · intro hindependent edge hedge hphysical
    apply (hindependent edge hedge).2
    apply (SimpleGraph.labelledExtension_reachable_iff_componentQuotient
      H GridEdge.primalEndpoints (S.erase edge)
        (Sum.inl edge.primalEndpoints.1)
        (Sum.inl edge.primalEndpoints.2)).mp
    apply (physicalExtension_reachable_iff_labelledExtension H
      (S.erase edge) _ _).mp hphysical

/-- Component endpoints of a physical repair edge. -/
def cropRepairComponentEnds {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B) (edge : GridEdge m n) :
    (cropInitialForcedGraph e F).ConnectedComponent ×
      (cropInitialForcedGraph e F).ConnectedComponent :=
  SimpleGraph.componentEnds (cropInitialForcedGraph e F)
    GridEdge.primalEndpoints edge

/-- Physical repair edges parallel to `edge` after contracting the components
of the initial forced graph.  Equality is unordered because quotient edges are
undirected. -/
noncomputable def cropRepairParallelFiber {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (edge : GridEdge m n) :
    Finset (GridEdge m n) := by
  classical
  exact (physicalCropRepairEdges e F R).filter fun other =>
    s((cropRepairComponentEnds e F other).1,
      (cropRepairComponentEnds e F other).2) =
    s((cropRepairComponentEnds e F edge).1,
      (cropRepairComponentEnds e F edge).2)

@[simp] theorem mem_cropRepairParallelFiber {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (edge other : GridEdge m n) :
    other ∈ cropRepairParallelFiber e F R edge ↔
      other ∈ physicalCropRepairEdges e F R ∧
        s((cropRepairComponentEnds e F other).1,
          (cropRepairComponentEnds e F other).2) =
        s((cropRepairComponentEnds e F edge).1,
          (cropRepairComponentEnds e F edge).2) := by
  classical
  simp [cropRepairParallelFiber]

/-- The labelled component quotient retaining every physical repair edge,
including parallel fibers. -/
def cropRepairComponentQuotient {m n : Nat} [DecidableEq B]
    (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) :=
  SimpleGraph.labelledComponentQuotient (cropInitialForcedGraph e F)
    GridEdge.primalEndpoints (physicalCropRepairEdges e F R)

/-- Exact contraction characterization of crop-repair admissibility.  Physical
grid edges are subdivided only for the label-retaining quotient, so adjacent
repair vertices still contribute one shared `GridEdge` label. -/
theorem cropRepairAdmissible_iff_componentQuotient_isAcyclic
    {m n : Nat} [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (hR : IsCropRepairSet e F R)
    (hcrop : (cropInitialForcedGraph e F).IsAcyclic) :
    CropRepairAdmissible (gridGraph m n) e F R ↔
      (cropRepairComponentQuotient e F R).IsAcyclic := by
  rw [CropRepairAdmissible, forcedEdgeGraph_crop_union_repair_eq e F R hR]
  change (cropInitialForcedGraph e F ⊔
      physicalGridEdgeGraph (physicalCropRepairEdges e F R)).IsAcyclic ↔ _
  rw [physicalCropExtension_isAcyclic_iff_labelledExtension e F R hcrop]
  exact SimpleGraph.labelledExtension_isAcyclic_iff_componentQuotient
    (cropInitialForcedGraph e F) hcrop GridEdge.primalEndpoints
      (physicalCropRepairEdges e F R)

/-- A disjoint crop repair is admissible exactly when its physical-edge
labelled component quotient is a forest. -/
theorem cropRepairAdmissible_iff_labelledQuotientForest
    {m n : Nat} [DecidableEq B] (e : GridVertex m n ↪ B) (F : Finset B)
    (R : Finset (GridVertex m n)) (hR : IsCropRepairSet e F R)
    (hcrop : (cropInitialForcedGraph e F).IsAcyclic) :
    CropRepairAdmissible (gridGraph m n) e F R ↔
      SimpleGraph.LabelledQuotientForest (cropInitialForcedGraph e F)
        GridEdge.primalEndpoints (physicalCropRepairEdges e F R) := by
  simpa [SimpleGraph.LabelledQuotientForest, cropRepairComponentQuotient] using
    cropRepairAdmissible_iff_componentQuotient_isAcyclic e F R hR hcrop

end GridGraphs
