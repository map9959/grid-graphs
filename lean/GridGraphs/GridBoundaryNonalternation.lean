import GridGraphs.GridBoundaryCycle
import GridGraphs.GridCrop
import GridGraphs.GridCrosscutParity

/-!
# Boundary path crossing and component nonalternation

This file develops the graph-theoretic support and component lemmas used by a
rectangular boundary-crossing argument, together with persistence of induced
components across overlapping crops.
-/

namespace GridGraphs

open SimpleGraph

/-- Four vertices cannot carry component labels in the pattern `C,D,C,D`.
This formulation also covers coincident endpoint labels without requiring a
decidable equality on connected components. -/
def ComponentLabelsNonalternating {V : Type*} (G : SimpleGraph V)
    (a b c d : V) : Prop :=
  ∀ (C D : G.ConnectedComponent),
    a ∈ C.supp → c ∈ C.supp → b ∈ D.supp → d ∈ D.supp → C = D

/-- A walk lies entirely in the connected component containing its first
vertex. -/
theorem Walk.support_subset_connectedComponent {V : Type*}
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (C : G.ConnectedComponent) (hu : u ∈ C.supp) :
    ∀ ⦃x : V⦄, x ∈ p.support → x ∈ C.supp := by
  classical
  intro x hx
  rw [ConnectedComponent.mem_supp_iff] at hu ⊢
  exact (ConnectedComponent.sound (p.takeUntil x hx).reachable).symm.trans hu

/-- Two walk supports have no vertex in common. -/
def WalkSupportsDisjoint {V : Type*} {G : SimpleGraph V}
    {u v s t : V} (p : G.Walk u v) (q : G.Walk s t) : Prop :=
  ¬∃ x : V, x ∈ p.support ∧ x ∈ q.support

/-- Walks starting in distinct connected components have disjoint vertex
supports. -/
theorem Walk.disjoint_support_of_mem_distinct_components {V : Type*}
    {G : SimpleGraph V} {u v s t : V}
    (p : G.Walk u v) (q : G.Walk s t)
    (C D : G.ConnectedComponent) (hu : u ∈ C.supp) (hs : s ∈ D.supp)
    (hCD : C ≠ D) : WalkSupportsDisjoint p q := by
  rintro ⟨x, hxp, hxq⟩
  apply hCD
  exact ConnectedComponent.eq_of_common_vertex
    (Walk.support_subset_connectedComponent p C hu hxp)
    (Walk.support_subset_connectedComponent q D hs hxq)

/-- Contrapositive form convenient for proving the geometric crossing theorem:
an alternating pair of paths cannot live in two distinct components. -/
theorem not_endpointPathsIntersect_of_distinct_component_paths
    {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (C D : G.ConnectedComponent) (ha : a ∈ C.supp) (hb : b ∈ D.supp)
    (hCD : C ≠ D) (p : G.Walk a c) (q : G.Walk b d) :
    ¬∃ x : V, x ∈ p.support ∧ x ∈ q.support := by
  intro h
  obtain ⟨x, hxp, hxq⟩ := h
  exact hCD (ConnectedComponent.eq_of_common_vertex
    (Walk.support_subset_connectedComponent p C ha hxp)
    (Walk.support_subset_connectedComponent q D hb hxq))

/-- Component labels around the boundary of a grid subgraph cannot alternate.
-/
theorem componentLabelsNonalternating_gridBoundary
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (G : SimpleGraph (GridVertex m n)) (hG : G ≤ gridGraph m n)
    (a b c d : GridBoundaryPosition m n)
    (halt : CyclicallyAlternating (gridBoundaryLength_pos hm hn) a c b d) :
    ComponentLabelsNonalternating G
      (gridBoundaryVertex hm hn a) (gridBoundaryVertex hm hn b)
      (gridBoundaryVertex hm hn c) (gridBoundaryVertex hm hn d) := by
  intro C D ha hc hb hd
  by_contra hCD
  rw [ConnectedComponent.mem_supp_iff] at ha hc hb hd
  have hac : G.Reachable (gridBoundaryVertex hm hn a)
      (gridBoundaryVertex hm hn c) :=
    ConnectedComponent.exact (ha.trans hc.symm)
  have hbd : G.Reachable (gridBoundaryVertex hm hn b)
      (gridBoundaryVertex hm hn d) :=
    ConnectedComponent.exact (hb.trans hd.symm)
  obtain ⟨p, hp⟩ := hac.exists_isPath
  obtain ⟨q, hq⟩ := hbd.exists_isPath
  let inclusion : G →g gridGraph m n :=
    { toFun := id
      map_rel' := fun h => hG h }
  let p' := p.map inclusion
  let q' := q.map inclusion
  have hp' : p'.IsPath :=
    Walk.map_isPath_of_injective (by intro x y h; exact h) hp
  obtain ⟨x, hxp, hxq⟩ :=
    grid_paths_intersect_of_cyclicallyAlternating hm hn p' hp' q' halt
  apply hCD
  apply ConnectedComponent.eq_of_common_vertex
  · apply Walk.support_subset_connectedComponent p C
      (by simpa [ConnectedComponent.mem_supp_iff] using ha)
    simpa [p', inclusion, Walk.support_map] using hxp
  · apply Walk.support_subset_connectedComponent q D
      (by simpa [ConnectedComponent.mem_supp_iff] using hb)
    simpa [q', inclusion, Walk.support_map] using hxq

/-! ## Persistence across overlapping induced crops -/

/-- The ambient component containing an induced-subgraph component. -/
def inducedComponentAmbient {V : Type*} (G : SimpleGraph V) (S : Set V)
    (C : (G.induce S).ConnectedComponent) : G.ConnectedComponent :=
  C.map
    { toFun := fun x => x.1
      map_rel' := fun h => h }

/-- A component of an induced crop containing `x` maps to the ambient
component containing `x`. -/
theorem inducedComponentAmbient_eq_of_mem {V : Type*} {G : SimpleGraph V}
    {S : Set V} (C : (G.induce S).ConnectedComponent) {x : V} (hxS : x ∈ S)
    (hxC : (⟨x, hxS⟩ : S) ∈ C.supp) :
    inducedComponentAmbient G S C = G.connectedComponentMk x := by
  rw [ConnectedComponent.mem_supp_iff] at hxC
  rw [← hxC]
  rfl

/-- Components found in two induced crops persist as the same ambient
component whenever they contain a common vertex in the crop overlap. -/
theorem inducedComponents_same_ambient_of_overlap {V : Type*}
    {G : SimpleGraph V} {S T : Set V}
    (C : (G.induce S).ConnectedComponent)
    (D : (G.induce T).ConnectedComponent) {x : V}
    (hxS : x ∈ S) (hxT : x ∈ T)
    (hxC : (⟨x, hxS⟩ : S) ∈ C.supp)
    (hxD : (⟨x, hxT⟩ : T) ∈ D.supp) :
    inducedComponentAmbient G S C = inducedComponentAmbient G T D := by
  rw [inducedComponentAmbient_eq_of_mem C hxS hxC,
    inducedComponentAmbient_eq_of_mem D hxT hxD]

end GridGraphs
