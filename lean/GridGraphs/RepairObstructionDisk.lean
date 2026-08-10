import GridGraphs.CyclicCropBoundarySignature
import GridGraphs.GridDual

/-!
# Repair obstruction cycles and forest-path intersections

This file isolates the unconditional combinatorics available for a blocked
repair insertion.  A fresh physical label whose two attachment components are
already connected in the current labelled quotient makes the quotient cyclic.
The resulting cycle is retained as a noncomputable certificate, so parallel
physical edges are never identified.

The path lemmas record the corresponding tree fact needed by any later
uncrossing argument: a path in a forest is convex, and two forest paths have a
path-connected intersection whenever that intersection is nonempty.
-/

namespace SimpleGraph

variable {V E : Type*} {G : SimpleGraph V}

/-- The support of a path in a forest is convex: the unique path between two
of its vertices stays in its support. -/
theorem IsAcyclic.path_support_convex (hG : G.IsAcyclic)
    {a b u v : V} (p : G.Walk a b) (_hp : p.IsPath)
    (q : G.Walk u v) (hq : q.IsPath)
    (hu : u ∈ p.support) (hv : v ∈ p.support) :
    ∀ x ∈ q.support, x ∈ p.support := by
  classical
  let S : Set V := {x | x ∈ p.support}
  let uS : S := ⟨u, hu⟩
  let vS : S := ⟨v, hv⟩
  have hconn : (G.induce S).Connected := p.connected_induce_support
  obtain ⟨r⟩ := hconn uS vS
  let inclusion : G.induce S →g G :=
    (SimpleGraph.Embedding.comap (Function.Embedding.subtype S) G).toHom
  let rG : G.Walk u v :=
    (r.toPath : (G.induce S).Walk uS vS).map inclusion
  have hrG : rG.IsPath := by
    exact Walk.map_isPath_of_injective Subtype.val_injective r.toPath.isPath
  have heq : q = rG := by
    exact congrArg Subtype.val
      (hG.path_unique (⟨q, hq⟩ : G.Path u v) (⟨rG, hrG⟩ : G.Path u v))
  intro x hx
  rw [heq] at hx
  change x ∈ ((r.toPath : (G.induce S).Walk uS vS).map inclusion).support at hx
  rw [Walk.support_map, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact y.property

/-- If two paths in a forest meet, every pair of common vertices is joined by
a path whose whole support remains in their intersection.  Thus their
intersection is a connected subpath in the intrinsic graph-theoretic sense. -/
theorem IsAcyclic.path_support_intersection_connected (hG : G.IsAcyclic)
    {a b c d : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk c d) (hq : q.IsPath) {u v : V}
    (hup : u ∈ p.support) (huq : u ∈ q.support)
    (hvp : v ∈ p.support) (hvq : v ∈ q.support) :
    ∃ r : G.Walk u v, r.IsPath ∧
      ∀ x ∈ r.support, x ∈ p.support ∧ x ∈ q.support := by
  classical
  have huv : G.Reachable u v := by
    let S : Set V := {x | x ∈ p.support}
    have hconn : (G.induce S).Connected := p.connected_induce_support
    let uS : S := ⟨u, hup⟩
    let vS : S := ⟨v, hvp⟩
    obtain ⟨r⟩ := hconn uS vS
    let inclusion : G.induce S →g G :=
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype S) G).toHom
    exact ⟨r.map inclusion⟩
  obtain ⟨r, hr⟩ := huv.exists_isPath
  refine ⟨r, hr, ?_⟩
  intro x hx
  exact ⟨hG.path_support_convex p hp r hr hup hvp x hx,
    hG.path_support_convex q hq r hr huq hvq x hx⟩

/-- A candidate-owned obstruction consists of an old forest path closed by
one or two fresh edges at the candidate.  In the two-edge case the candidate
does not occur on the old path, exactly the condition needed for simplicity. -/
inductive CandidateOwnedClosing (G H : SimpleGraph V) (u : V)
    | one (v : V) (adj : G.Adj u v) (fresh : ¬H.Adj u v)
        (path : H.Walk u v) (path_isPath : path.IsPath)
    | two (a b : V) (a_ne_b : a ≠ b) (adj_a : G.Adj u a)
        (adj_b : G.Adj u b) (fresh_a : ¬H.Adj u a)
        (fresh_b : ¬H.Adj u b) (path : H.Walk a b)
        (path_isPath : path.IsPath) (owner_not_mem : u ∉ path.support)

namespace CandidateOwnedClosing

variable {H : SimpleGraph V} {u : V}

/-- The literal primal cycle obtained by closing the old path at its owner. -/
def cycle (hHG : H ≤ G) (C : CandidateOwnedClosing G H u) : G.Walk u u :=
  match C with
  | .one _ huv _ p _ => Walk.cons huv (p.mapLe hHG).reverse
  | .two _ _ _ hua hub _ _ p _ _ =>
      Walk.cons hua ((p.mapLe hHG).concat hub.symm)

/-- The constructed primal obstruction is a simple cycle. -/
theorem cycle_isCycle (hHG : H ≤ G) (C : CandidateOwnedClosing G H u) :
    (C.cycle hHG).IsCycle := by
  classical
  cases C with
  | one v huv hnew p hp =>
      rw [cycle, Walk.cons_isCycle_iff]
      refine ⟨hp.mapLe hHG |>.reverse, ?_⟩
      intro hedge
      apply hnew
      have hedge' : s(u, v) ∈ p.edges := by simpa using hedge
      simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet hedge'
  | two a b hab hua hub hnewa hnewb p hp hunot =>
      rw [cycle, Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · exact (hp.mapLe hHG).concat (by
          simpa [Walk.support_map] using hunot) hub.symm
      · simp only [Walk.edges_concat]
        simp
        constructor
        · intro hedge
          apply hnewa
          have hedge' : s(u, a) ∈ p.edges := by simpa using hedge
          simpa [SimpleGraph.mem_edgeSet] using p.edges_subset_edgeSet hedge'
        · constructor
          · intro hubEq hauEq
            exact hab (hauEq.trans hubEq)
          · exact hab

/-- Every non-forest edge of the obstruction cycle is incident to its current
candidate owner. -/
theorem edge_mem_old_or_incident (hHG : H ≤ G)
    (C : CandidateOwnedClosing G H u) {edge : Sym2 V}
    (hedge : edge ∈ (C.cycle hHG).edges) :
    edge ∈ H.edgeSet ∨ u ∈ edge := by
  classical
  cases C with
  | one v huv hnew p hp =>
      simp only [cycle, Walk.edges_cons, Walk.edges_reverse, List.mem_cons,
        List.mem_reverse] at hedge
      rcases hedge with rfl | hedge
      · exact Or.inr (Sym2.mem_iff.mpr (Or.inl rfl))
      · apply Or.inl
        apply p.edges_subset_edgeSet
        simpa using hedge
  | two a b hab hua hub hnewa hnewb p hp hunot =>
      simp only [cycle, Walk.edges_cons, Walk.edges_concat, List.mem_cons] at hedge
      simp at hedge
      rcases hedge with rfl | hedge | rfl
      · exact Or.inr (Sym2.mem_iff.mpr (Or.inl rfl))
      · apply Or.inl
        apply p.edges_subset_edgeSet
        simpa using hedge
      · exact Or.inr (Sym2.mem_iff.mpr (Or.inr rfl))

/-- Exact support of the obstruction: the owner together with the old forest
path. -/
theorem mem_cycle_support_iff (hHG : H ≤ G)
    (C : CandidateOwnedClosing G H u) (x : V) :
    x ∈ (C.cycle hHG).support ↔ x = u ∨
      match C with
      | .one _ _ _ p _ => x ∈ p.support
      | .two _ _ _ _ _ _ _ p _ _ => x ∈ p.support := by
  cases C with
  | one => simp [cycle, Walk.support_map]
  | two =>
      simp [cycle, Walk.support_map]
      tauto

/-- Vertices of the old forest path underlying an owned closing. -/
def oldPathSupport (C : CandidateOwnedClosing G H u) : Set V :=
  match C with
  | .one _ _ _ p _ => {x | x ∈ p.support}
  | .two _ _ _ _ _ _ _ p _ _ => {x | x ∈ p.support}

/-- Owner-preserving uncrossing available without extra hypotheses: the old
parts of two owned obstruction cycles meet in a connected forest subpath.  No
candidate spoke is exchanged or reassigned. -/
theorem oldPathSupport_intersection_connected (hH : H.IsAcyclic)
    {u₁ u₂ : V} (C : CandidateOwnedClosing G H u₁)
    (D : CandidateOwnedClosing G H u₂) {x y : V}
    (hxC : x ∈ C.oldPathSupport) (hxD : x ∈ D.oldPathSupport)
    (hyC : y ∈ C.oldPathSupport) (hyD : y ∈ D.oldPathSupport) :
    ∃ r : H.Walk x y, r.IsPath ∧
      ∀ z ∈ r.support, z ∈ C.oldPathSupport ∧ z ∈ D.oldPathSupport := by
  cases C with
  | one v huv hnew p hp =>
      cases D with
      | one w huw hneww q hq =>
          exact hH.path_support_intersection_connected p hp q hq hxC hxD hyC hyD
      | two a b hab hua hub hnewa hnewb q hq huq =>
          exact hH.path_support_intersection_connected p hp q hq hxC hxD hyC hyD
  | two a b hab hua hub hnewa hnewb p hp hup =>
      cases D with
      | one w huw hneww q hq =>
          exact hH.path_support_intersection_connected p hp q hq hxC hxD hyC hyD
      | two c d hcd huc hud hnewc hnewd q hq huq =>
          exact hH.path_support_intersection_connected p hp q hq hxC hxD hyC hyD

end CandidateOwnedClosing

end SimpleGraph

namespace GridGraphs

open Finset SimpleGraph

/-- A failed insertion condition in a current forced forest. -/
structure BlockedForcedInsertion {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Prop where
  owner_not_forced : u ∉ F
  currentForest : (forcedEdgeGraph G F).IsAcyclic
  blocked : ¬ForcedInsertionCondition G F u

private theorem reachable_of_mem_path_support {V : Type*} {G : SimpleGraph V}
    {a b x y : V} (p : G.Walk a b) (hx : x ∈ p.support)
    (hy : y ∈ p.support) : G.Reachable x y := by
  classical
  let S : Set V := {z | z ∈ p.support}
  have hconn : (G.induce S).Connected := p.connected_induce_support
  let xS : S := ⟨x, hx⟩
  let yS : S := ⟨y, hy⟩
  obtain ⟨q⟩ := hconn xS yS
  let inclusion : G.induce S →g G :=
    (SimpleGraph.Embedding.comap (Function.Embedding.subtype S) G).toHom
  exact ⟨q.map inclusion⟩

/-- A blocked insertion canonically yields an old path closed by one or two
fresh candidate-owned edges. -/
noncomputable def BlockedForcedInsertion.canonicalClosing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : Set V} {u : V}
    (h : BlockedForcedInsertion G F u) :
    CandidateOwnedClosing G (forcedEdgeGraph G F) u := by
  classical
  have hexists : Nonempty
      (CandidateOwnedClosing G (forcedEdgeGraph G F) u) := by
    have hblocked := h.blocked
    unfold ForcedInsertionCondition at hblocked
    push_neg at hblocked
    obtain ⟨a, ha, b, hb, hab, habReach⟩ := hblocked
    obtain ⟨p, hp⟩ := habReach.exists_isPath
    rcases ha with rfl | ⟨hua, haF⟩
    · have hb' : G.Adj a b ∧ b ∉ F := by
        rcases hb with rfl | hb
        · exact (hab rfl).elim
        · exact hb
      exact ⟨.one b hb'.1
        (fun hold => hold.2.elim h.owner_not_forced hb'.2) p hp⟩
    · rcases hb with rfl | ⟨hub, hbF⟩
      · exact ⟨.one a hua (fun hold => hold.2.elim h.owner_not_forced haF)
          p.reverse hp.reverse⟩
      · by_cases huPath : u ∈ p.support
        · have hau : (forcedEdgeGraph G F).Reachable a u :=
            reachable_of_mem_path_support p p.start_mem_support huPath
          obtain ⟨q, hq⟩ := hau.symm.exists_isPath
          exact ⟨.one a hua (fun hold => hold.2.elim h.owner_not_forced haF) q hq⟩
        · exact ⟨.two a b hab hua hub
            (fun hold => hold.2.elim h.owner_not_forced haF)
            (fun hold => hold.2.elim h.owner_not_forced hbF) p hp huPath⟩
  exact Classical.choice hexists

theorem BlockedForcedInsertion.canonicalClosing_isCycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : Set V} {u : V}
    (h : BlockedForcedInsertion G F u) :
    (h.canonicalClosing.cycle (forcedEdgeGraph_le G F)).IsCycle :=
  h.canonicalClosing.cycle_isCycle (forcedEdgeGraph_le G F)

section Grid

variable {m n : Nat} {F : Set (GridVertex m n)} {u : GridVertex m n}

private theorem gridEdge_mem_next_bundle_of_fresh_incident
    {B : Type*} [DecidableEq B] (e : GridVertex m n ↪ B) (A : Finset B)
    (R : Finset (GridVertex m n)) (u : GridVertex m n)
    (edge : GridEdge m n)
    (hincident : edge.Incident u)
    (hfresh : ¬(forcedEdgeGraph (gridGraph m n)
      ((↑(cropForcedSet e A) : Set (GridVertex m n)) ∪ (↑R : Set _))).Adj
        edge.primalEndpoints.1 edge.primalEndpoints.2) :
    edge ∈ cropRepairBundle e A (insert u R) u := by
  have hadj : (gridGraph m n).Adj edge.primalEndpoints.1
      edge.primalEndpoints.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    exact GridEdge.primalSym2_mem_gridGraph_edgeSet edge
  have hfirst : edge.primalEndpoints.1 ∉ cropForcedSet e A := by
    intro hmem
    apply hfresh
    exact ⟨hadj, Or.inl (Or.inl hmem)⟩
  have hsecond : edge.primalEndpoints.2 ∉ cropForcedSet e A := by
    intro hmem
    apply hfresh
    exact ⟨hadj, Or.inr (Or.inl hmem)⟩
  rw [mem_cropRepairBundle, mem_physicalCropRepairEdges]
  refine ⟨⟨?_, hfirst, hsecond⟩, hincident⟩
  rcases hincident with hfirstu | hsecondu
  · exact Or.inl (by simp [hfirstu])
  · exact Or.inr (by simp [hsecondu])

/-- Exact bundle compatibility for candidate ownership.  Any physical grid
edge used by the obstruction but absent from the current forced forest is in
the bundle of the vertex being inserted now. -/
theorem BlockedForcedInsertion.obstruction_new_edge_mem_next_bundle
    {B : Type*} [DecidableEq B] (e : GridVertex m n ↪ B) (A : Finset B)
    (R : Finset (GridVertex m n))
    (h : BlockedForcedInsertion (gridGraph m n)
      ((↑(cropForcedSet e A) : Set (GridVertex m n)) ∪ (↑R : Set _)) u)
    (edge : GridEdge m n)
    (hcycle : edge.primalSym2 ∈ (h.canonicalClosing.cycle
      (forcedEdgeGraph_le (gridGraph m n)
        ((↑(cropForcedSet e A) : Set (GridVertex m n)) ∪ (↑R : Set _)))).edges)
    (hfresh : edge.primalSym2 ∉ (forcedEdgeGraph (gridGraph m n)
      ((↑(cropForcedSet e A) : Set (GridVertex m n)) ∪ (↑R : Set _))).edgeSet) :
    edge ∈ cropRepairBundle e A (insert u R) u := by
  have howner := h.canonicalClosing.edge_mem_old_or_incident
    (forcedEdgeGraph_le (gridGraph m n)
      ((↑(cropForcedSet e A) : Set (GridVertex m n)) ∪ (↑R : Set _))) hcycle
  rcases howner with hold | hincident
  · exact (hfresh hold).elim
  · apply gridEdge_mem_next_bundle_of_fresh_incident e A R u edge
    · rw [GridEdge.primalSym2, Sym2.mem_iff] at hincident
      exact hincident.elim (fun hu => Or.inl hu.symm) (fun hu => Or.inr hu.symm)
    · intro hadj
      apply hfresh
      simpa [SimpleGraph.mem_edgeSet, GridEdge.primalSym2] using hadj

/-- The primal obstruction disk is the finite dual interior of the canonical
candidate-owned grid cycle. -/
noncomputable def BlockedForcedInsertion.obstructionDisk
    (h : BlockedForcedInsertion (gridGraph m n) F u) :
    Finset (GridFace m n) :=
  cycleInteriorFaces (h.canonicalClosing.cycle
    (forcedEdgeGraph_le (gridGraph m n) F))

@[simp] theorem BlockedForcedInsertion.out_not_mem_obstructionDisk
    (h : BlockedForcedInsertion (gridGraph m n) F u) :
    GridFace.out ∉ h.obstructionDisk :=
  out_not_mem_cycleInteriorFaces _

/-- Every canonical primal obstruction cuts off at least one bounded grid
face. -/
theorem BlockedForcedInsertion.obstructionDisk_nonempty
    (h : BlockedForcedInsertion (gridGraph m n) F u) :
    h.obstructionDisk.Nonempty := by
  let c := h.canonicalClosing.cycle (forcedEdgeGraph_le (gridGraph m n) F)
  have hc : c.IsCycle := h.canonicalClosing_isCycle
  have hle : gridGraph m n ≤ forcedEdgeGraph (gridGraph m n)
      (↑(∅ : Finset (GridVertex m n)) : Set (GridVertex m n))ᶜ := by
    intro x y hxy
    exact ⟨hxy, by simp⟩
  let c' : (forcedEdgeGraph (gridGraph m n)
      (↑(∅ : Finset (GridVertex m n)) : Set (GridVertex m n))ᶜ).Walk u u :=
    c.mapLe hle
  have hc' : c'.IsCycle := hc.mapLe hle
  have hencloses : GridCycleEnclosesBoundedFace :=
    gridCycleEnclosesBoundedFace_of_rowRayParity gridCycleRowRayParity
  have hinterior := hencloses (∅ : Finset (GridVertex m n)) c' hc'
  have hedges : c'.edges = c.edges := by simp [c', Walk.edges_map]
  have hdual : cycleComplementDualGraph c' = cycleComplementDualGraph c := by
    ext f g
    simp only [cycleComplementDualGraph, hedges]
  have hinteriorEq : cycleInteriorFaces c' = cycleInteriorFaces c := by
    ext f
    rw [mem_cycleInteriorFaces_iff, mem_cycleInteriorFaces_iff]
    constructor <;> intro hn hreach <;> apply hn
    · simpa only [hdual] using hreach
    · simpa only [hdual] using hreach
  rw [hinteriorEq] at hinterior
  simpa [BlockedForcedInsertion.obstructionDisk, c] using hinterior

/-- Disk nesting is literal inclusion of the dual interior face sets. -/
def BlockedForcedInsertion.DiskNested
    (h k : BlockedForcedInsertion (gridGraph m n) F u) : Prop :=
  h.obstructionDisk ⊆ k.obstructionDisk

theorem BlockedForcedInsertion.diskNested_refl
    (h : BlockedForcedInsertion (gridGraph m n) F u) : h.DiskNested h :=
  Finset.Subset.rfl

theorem BlockedForcedInsertion.diskNested_trans
    {h k l : BlockedForcedInsertion (gridGraph m n) F u}
    (hhk : h.DiskNested k) (hkl : k.DiskNested l) : h.DiskNested l :=
  hhk.trans hkl

end Grid

end GridGraphs
