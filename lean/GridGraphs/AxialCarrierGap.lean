import GridGraphs.StraightForcedComponents

/-!
# Axial gaps between straight forced components

This file defines the finite geometric invariant suggested by straight induced
forced components.  It deliberately contains no estimate for the invariant.
An axial carrier gap is a nonempty open row or column interval in the
complement of `F`, bounded by two distinct non-singleton components of the
graph induced by `F`.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The two orientations of a non-singleton straight grid component. -/
inductive AxialOrientation
  | horizontal
  | vertical
  deriving DecidableEq

namespace AxialOrientation

instance : Fintype AxialOrientation :=
  ⟨{horizontal, vertical}, by intro x; cases x <;> simp⟩

/-- The coordinate which is constant along an oriented line. -/
def line {m n : Nat} : AxialOrientation → GridVertex m n → Nat
  | .horizontal, v => v.1.val
  | .vertical, v => v.2.val

/-- The coordinate which increases along an oriented line. -/
def position {m n : Nat} : AxialOrientation → GridVertex m n → Nat
  | .horizontal, v => v.2.val
  | .vertical, v => v.1.val

theorem ext_vertex {m n : Nat} (o : AxialOrientation) {u v : GridVertex m n}
    (hline : o.line u = o.line v) (hpos : o.position u = o.position v) : u = v := by
  cases o
  · apply Prod.ext <;> apply Fin.ext
    · exact hline
    · exact hpos
  · apply Prod.ext <;> apply Fin.ext
    · exact hpos
    · exact hline

end AxialOrientation

/-- A non-singleton component of the graph induced by `F`, together with its
straight orientation.  Proofs from `StraightForcedComponents` construct these
packages when the forced-edge graph is acyclic. -/
structure StraightInducedFComponent {m n : Nat} (F : Set (GridVertex m n)) where
  component : ((gridGraph m n).induce F).ConnectedComponent
  orientation : AxialOrientation
  nonSingleton : ∃ u v : F,
    u ∈ component.supp ∧ v ∈ component.supp ∧ u ≠ v
  straight : ∀ u ∈ component.supp, ∀ v ∈ component.supp,
    orientation.line u.1 = orientation.line v.1

namespace StraightInducedFComponent

variable {m n : Nat} {F : Set (GridVertex m n)}

/-- A non-singleton component cannot carry both straight orientations. -/
theorem orientation_eq_of_component_eq
    (C D : StraightInducedFComponent F) (hcomponent : C.component = D.component) :
    C.orientation = D.orientation := by
  obtain ⟨u, v, hu, hv, huv⟩ := C.nonSingleton
  have huD : u ∈ D.component.supp := by simpa [hcomponent] using hu
  have hvD : v ∈ D.component.supp := by simpa [hcomponent] using hv
  have hC := C.straight u hu v hv
  have hD := D.straight u huD v hvD
  cases hCaxis : C.orientation <;> cases hDaxis : D.orientation
  · rfl
  · exfalso
    apply huv
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simpa [AxialOrientation.line, hCaxis] using hC
    · simpa [AxialOrientation.line, hDaxis] using hD
  · exfalso
    apply huv
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simpa [AxialOrientation.line, hDaxis] using hD
    · simpa [AxialOrientation.line, hCaxis] using hC
  · rfl

@[ext] theorem ext (C D : StraightInducedFComponent F)
    (hcomponent : C.component = D.component) : C = D := by
  have horientation := C.orientation_eq_of_component_eq D hcomponent
  cases C
  cases D
  simp_all

/-- Acyclicity makes every non-singleton induced component into a straight
component with a uniquely determined orientation. -/
theorem existsUnique_of_isAcyclic
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent)
    (hnon : ∃ u v : F, u ∈ C.supp ∧ v ∈ C.supp ∧ u ≠ v) :
    ∃! K : StraightInducedFComponent F, K.component = C := by
  rcases induced_forced_connectedComponent_straight hacyc C with hrow | hcol
  · obtain ⟨r, hr⟩ := hrow
    let K : StraightInducedFComponent F :=
      { component := C
        orientation := .horizontal
        nonSingleton := hnon
        straight := by
          intro u hu v hv
          exact congrArg Fin.val ((hr u hu).trans (hr v hv).symm) }
    refine ⟨K, rfl, ?_⟩
    intro D hD
    exact D.ext K hD
  · obtain ⟨c, hc⟩ := hcol
    let K : StraightInducedFComponent F :=
      { component := C
        orientation := .vertical
        nonSingleton := hnon
        straight := by
          intro u hu v hv
          exact congrArg Fin.val ((hc u hu).trans (hc v hv).symm) }
    refine ⟨K, rfl, ?_⟩
    intro D hD
    exact D.ext K hD

end StraightInducedFComponent

/-- A consecutive axial gap between two non-singleton straight components.
The endpoints are listed in increasing axial order.  The open interval is
required to be nonempty and to contain no vertex of `F`; in particular,
singleton and perpendicular components break rather than extend a gap. -/
structure AxialCarrierGap {m n : Nat} (F : Set (GridVertex m n)) where
  leftComponent : StraightInducedFComponent F
  rightComponent : StraightInducedFComponent F
  leftEndpoint : F
  rightEndpoint : F
  left_mem : leftEndpoint ∈ leftComponent.component.supp
  right_mem : rightEndpoint ∈ rightComponent.component.supp
  same_orientation : leftComponent.orientation = rightComponent.orientation
  same_line : leftComponent.orientation.line leftEndpoint.1 =
    leftComponent.orientation.line rightEndpoint.1
  nonempty : leftComponent.orientation.position leftEndpoint.1 + 1 <
    leftComponent.orientation.position rightEndpoint.1
  interior_compl : ∀ z : GridVertex m n,
    leftComponent.orientation.line z =
        leftComponent.orientation.line leftEndpoint.1 →
      leftComponent.orientation.position leftEndpoint.1 <
        leftComponent.orientation.position z →
      leftComponent.orientation.position z <
        leftComponent.orientation.position rightEndpoint.1 →
      z ∉ F
  components_ne : leftComponent.component ≠ rightComponent.component

/-- The finite type whose cardinality is the axial carrier gap invariant. -/
abbrev axialCarrierGap {m n : Nat} (F : Set (GridVertex m n)) :=
  AxialCarrierGap F

namespace AxialCarrierGap

variable {m n : Nat} {F : Set (GridVertex m n)}

/-- The open coordinate interval underlying a gap. -/
noncomputable def vertices (g : AxialCarrierGap F) : Finset (GridVertex m n) := by
  classical
  exact Finset.univ.filter fun z =>
    g.leftComponent.orientation.line z =
        g.leftComponent.orientation.line g.leftEndpoint.1 ∧
      g.leftComponent.orientation.position g.leftEndpoint.1 <
        g.leftComponent.orientation.position z ∧
      g.leftComponent.orientation.position z <
        g.leftComponent.orientation.position g.rightEndpoint.1

@[simp] theorem mem_vertices_iff (g : AxialCarrierGap F) (z : GridVertex m n) :
    z ∈ g.vertices ↔
      g.leftComponent.orientation.line z =
          g.leftComponent.orientation.line g.leftEndpoint.1 ∧
        g.leftComponent.orientation.position g.leftEndpoint.1 <
          g.leftComponent.orientation.position z ∧
        g.leftComponent.orientation.position z <
          g.leftComponent.orientation.position g.rightEndpoint.1 := by
  classical
  simp [vertices]

/-- Every charged gap vertex lies in `U`, the complement of `F`. -/
theorem vertex_not_mem (g : AxialCarrierGap F) {z : GridVertex m n}
    (hz : z ∈ g.vertices) : z ∉ F := by
  rw [mem_vertices_iff] at hz
  exact g.interior_compl z hz.1 hz.2.1 hz.2.2

theorem vertices_disjoint_forced (g : AxialCarrierGap F) :
    Disjoint (↑g.vertices : Set (GridVertex m n)) F := by
  rw [Set.disjoint_left]
  intro z hz hF
  exact g.vertex_not_mem hz hF

/-- The left component is forced by the left endpoint. -/
theorem leftComponent_eq_connectedComponentMk (g : AxialCarrierGap F) :
    g.leftComponent.component =
      ((gridGraph m n).induce F).connectedComponentMk g.leftEndpoint := by
  exact (ConnectedComponent.mem_supp_iff _ _).mp g.left_mem |>.symm

/-- The right component is forced by the right endpoint. -/
theorem rightComponent_eq_connectedComponentMk (g : AxialCarrierGap F) :
    g.rightComponent.component =
      ((gridGraph m n).induce F).connectedComponentMk g.rightEndpoint := by
  exact (ConnectedComponent.mem_supp_iff _ _).mp g.right_mem |>.symm

theorem leftComponent_eq_of_leftEndpoint_eq (g h : AxialCarrierGap F)
    (hend : g.leftEndpoint = h.leftEndpoint) :
    g.leftComponent = h.leftComponent := by
  apply StraightInducedFComponent.ext
  rw [g.leftComponent_eq_connectedComponentMk,
    h.leftComponent_eq_connectedComponentMk, hend]

theorem rightComponent_eq_of_rightEndpoint_eq (g h : AxialCarrierGap F)
    (hend : g.rightEndpoint = h.rightEndpoint) :
    g.rightComponent = h.rightComponent := by
  apply StraightInducedFComponent.ext
  rw [g.rightComponent_eq_connectedComponentMk,
    h.rightComponent_eq_connectedComponentMk, hend]

/-- Once its ordered endpoints are fixed, all component and proof data of a
gap are unique. -/
@[ext] theorem ext (g h : AxialCarrierGap F)
    (hleft : g.leftEndpoint = h.leftEndpoint)
    (hright : g.rightEndpoint = h.rightEndpoint) : g = h := by
  have hleftComponent := g.leftComponent_eq_of_leftEndpoint_eq h hleft
  have hrightComponent := g.rightComponent_eq_of_rightEndpoint_eq h hright
  cases g
  cases h
  simp_all

/-- Two same-orientation consecutive gaps which share a vertex are the same
gap.  This is the endpoint uniqueness statement used by charging arguments. -/
theorem eq_of_common_vertex_of_same_orientation (g h : AxialCarrierGap F)
    (horient : g.leftComponent.orientation = h.leftComponent.orientation)
    {z : GridVertex m n} (hzg : z ∈ g.vertices) (hzh : z ∈ h.vertices) : g = h := by
  rw [mem_vertices_iff] at hzg hzh
  have hzh' :
      g.leftComponent.orientation.line z =
          g.leftComponent.orientation.line h.leftEndpoint.1 ∧
        g.leftComponent.orientation.position h.leftEndpoint.1 <
          g.leftComponent.orientation.position z ∧
        g.leftComponent.orientation.position z <
          g.leftComponent.orientation.position h.rightEndpoint.1 := by
    simpa only [← horient] using hzh
  have hlines : g.leftComponent.orientation.line g.leftEndpoint.1 =
      g.leftComponent.orientation.line h.leftEndpoint.1 := by
    rw [← hzg.1, hzh'.1]
  have hleftPos : g.leftComponent.orientation.position g.leftEndpoint.1 =
      g.leftComponent.orientation.position h.leftEndpoint.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hline : g.leftComponent.orientation.line h.leftEndpoint.1 =
          g.leftComponent.orientation.line g.leftEndpoint.1 := hlines.symm
      have hupper : g.leftComponent.orientation.position h.leftEndpoint.1 <
          g.leftComponent.orientation.position g.rightEndpoint.1 := by
        omega
      exact g.interior_compl h.leftEndpoint.1 hline hlt hupper h.leftEndpoint.2
    · have hline : h.leftComponent.orientation.line g.leftEndpoint.1 =
          h.leftComponent.orientation.line h.leftEndpoint.1 := by
        rw [← horient, hlines]
      have hlower : h.leftComponent.orientation.position h.leftEndpoint.1 <
          h.leftComponent.orientation.position g.leftEndpoint.1 := by
        rw [← horient]
        exact hgt
      have hupper : h.leftComponent.orientation.position g.leftEndpoint.1 <
          h.leftComponent.orientation.position h.rightEndpoint.1 := by
        simpa only [← horient] using (show
          g.leftComponent.orientation.position g.leftEndpoint.1 <
            g.leftComponent.orientation.position h.rightEndpoint.1 by omega)
      exact h.interior_compl g.leftEndpoint.1 hline hlower hupper g.leftEndpoint.2
  have hleft : g.leftEndpoint = h.leftEndpoint := by
    apply Subtype.ext
    exact AxialOrientation.ext_vertex g.leftComponent.orientation hlines hleftPos
  have hrightLine : g.leftComponent.orientation.line g.rightEndpoint.1 =
      g.leftComponent.orientation.line h.rightEndpoint.1 := by
    have hsame : g.leftComponent.orientation.line h.leftEndpoint.1 =
        g.leftComponent.orientation.line h.rightEndpoint.1 := by
      simpa only [← horient] using h.same_line
    exact g.same_line.symm.trans ((congrArg
      (fun e : F => g.leftComponent.orientation.line e.1) hleft).trans hsame)
  have hnonempty : g.leftComponent.orientation.position h.leftEndpoint.1 + 1 <
      g.leftComponent.orientation.position h.rightEndpoint.1 := by
    simpa only [← horient] using h.nonempty
  have hrightPos : g.leftComponent.orientation.position g.rightEndpoint.1 =
      g.leftComponent.orientation.position h.rightEndpoint.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hline : h.leftComponent.orientation.line g.rightEndpoint.1 =
          h.leftComponent.orientation.line h.leftEndpoint.1 := by
        rw [← horient, hrightLine]
        simpa only [← horient] using h.same_line.symm
      have hlower : h.leftComponent.orientation.position h.leftEndpoint.1 <
          h.leftComponent.orientation.position g.rightEndpoint.1 := by
        rw [← horient]
        omega
      have hupper : h.leftComponent.orientation.position g.rightEndpoint.1 <
          h.leftComponent.orientation.position h.rightEndpoint.1 := by
        rw [← horient]
        exact hlt
      exact h.interior_compl g.rightEndpoint.1 hline hlower hupper g.rightEndpoint.2
    · have hline : g.leftComponent.orientation.line h.rightEndpoint.1 =
          g.leftComponent.orientation.line g.leftEndpoint.1 := by
        rw [hrightLine.symm, g.same_line.symm]
      have hlower : g.leftComponent.orientation.position g.leftEndpoint.1 <
          g.leftComponent.orientation.position h.rightEndpoint.1 := by
        omega
      exact g.interior_compl h.rightEndpoint.1 hline hlower hgt h.rightEndpoint.2
  apply g.ext h hleft
  apply Subtype.ext
  exact AxialOrientation.ext_vertex g.leftComponent.orientation hrightLine hrightPos

/-- Distinct gaps of one orientation have disjoint open intervals. -/
theorem vertices_disjoint_of_same_orientation (g h : AxialCarrierGap F)
    (horient : g.leftComponent.orientation = h.leftComponent.orientation)
    (hne : g ≠ h) : Disjoint g.vertices h.vertices := by
  rw [Finset.disjoint_left]
  intro z hzg hzh
  exact hne (g.eq_of_common_vertex_of_same_orientation h horient hzg hzh)

/-- Perpendicular gaps need not be disjoint, but their intersection contains
at most one grid vertex. -/
theorem common_vertex_unique_of_orientation_ne (g h : AxialCarrierGap F)
    (horient : g.leftComponent.orientation ≠ h.leftComponent.orientation)
    {x y : GridVertex m n}
    (hxg : x ∈ g.vertices) (hxh : x ∈ h.vertices)
    (hyg : y ∈ g.vertices) (hyh : y ∈ h.vertices) : x = y := by
  rw [mem_vertices_iff] at hxg hxh hyg hyh
  have hgline : g.leftComponent.orientation.line x =
      g.leftComponent.orientation.line y := hxg.1.trans hyg.1.symm
  have hhline : h.leftComponent.orientation.line x =
      h.leftComponent.orientation.line y := hxh.1.trans hyh.1.symm
  cases hg : g.leftComponent.orientation <;>
      cases hh : h.leftComponent.orientation
  · exact (horient (hg.trans hh.symm)).elim
  · apply Prod.ext <;> apply Fin.ext
    · simpa [AxialOrientation.line, hg] using hgline
    · simpa [AxialOrientation.line, hh] using hhline
  · apply Prod.ext <;> apply Fin.ext
    · simpa [AxialOrientation.line, hh] using hhline
    · simpa [AxialOrientation.line, hg] using hgline
  · exact (horient (hg.trans hh.symm)).elim

end AxialCarrierGap

instance axialCarrierGapFinite {m n : Nat} (F : Set (GridVertex m n)) :
    Finite (axialCarrierGap F) :=
  Finite.of_injective
    (fun g : axialCarrierGap F => (g.leftEndpoint, g.rightEndpoint))
    (by
      intro g h heq
      exact g.ext h (congrArg Prod.fst heq) (congrArg Prod.snd heq))

noncomputable instance axialCarrierGapFintype {m n : Nat}
    (F : Set (GridVertex m n)) : Fintype (axialCarrierGap F) :=
  Fintype.ofFinite _

/-- The number of internal axial gaps.  No bound on this count is asserted in
this module. -/
noncomputable def axialCarrierGapCount {m n : Nat}
    (F : Set (GridVertex m n)) : Nat :=
  Fintype.card (axialCarrierGap F)

end GridGraphs
