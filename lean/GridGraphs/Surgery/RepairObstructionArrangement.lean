import GridGraphs.Surgery.RepairObstructionDisk

/-!
# Arrangement of repair obstruction disks

This file selects an inclusion-minimal obstruction disk from a finite set of
currently blocked candidates.  Minimality is deliberately only a statement
about the owned disks supplied by `RepairObstructionDisk`; no global
laminarity of grid cycles is assumed.

The boundary lemmas retain ownership.  Relative to a fixed obstruction
boundary, an edge of another owned closing is either shared, an old-forest
edge off the boundary, or an owner-incident spoke off the boundary.  For the
fresh spokes this gives the unconditional alternative needed by later repair
arguments: an off-boundary spoke is available, or all spokes discharge onto
the fixed boundary.  In the latter case there is exactly one discharge for a
one-spoke closing and exactly two for a two-spoke closing.
-/

namespace GridGraphs

open Finset SimpleGraph

section MinimalDisk

variable {m n : Nat} {F : Set (GridVertex m n)}

/-- An obstruction disk owned by a member of the current finite candidate
set, with no strictly smaller obstruction disk owned by another blocked
member of that set. -/
structure MinimalObstructionDisk
    (candidates : Finset (GridVertex m n)) where
  owner : GridVertex m n
  owner_mem : owner ∈ candidates
  blocked : BlockedForcedInsertion (gridGraph m n) F owner
  minimal : ∀ {v : GridVertex m n}, v ∈ candidates →
    ∀ h : BlockedForcedInsertion (gridGraph m n) F v,
      h.obstructionDisk ⊆ blocked.obstructionDisk →
        blocked.obstructionDisk ⊆ h.obstructionDisk

/-- Every nonempty finite collection of currently blocked candidates owns an
inclusion-minimal obstruction disk. -/
theorem exists_minimalObstructionDisk
    (candidates : Finset (GridVertex m n))
    (hexists : ∃ u ∈ candidates,
      BlockedForcedInsertion (gridGraph m n) F u) :
    Nonempty (MinimalObstructionDisk (F := F) candidates) := by
  classical
  let disks : Set (Finset (GridFace m n)) :=
    {D | ∃ u ∈ candidates,
      ∃ h : BlockedForcedInsertion (gridGraph m n) F u,
        h.obstructionDisk = D}
  obtain ⟨u, hu, hblocked⟩ := hexists
  have hmem : hblocked.obstructionDisk ∈ disks :=
    ⟨u, hu, hblocked, rfl⟩
  have hfinite : disks.Finite := Set.toFinite disks
  obtain ⟨D, _hDsub, hDmin⟩ := hfinite.exists_le_minimal hmem
  obtain ⟨v, hv, hblockedv, hD⟩ := hDmin.prop
  refine ⟨⟨v, hv, hblockedv, ?_⟩⟩
  intro w hw hblockedw hwv
  have hwmem : hblockedw.obstructionDisk ∈ disks :=
    ⟨w, hw, hblockedw, rfl⟩
  have hwD : hblockedw.obstructionDisk ≤ D := by
    simpa [← hD] using hwv
  have hDle := hDmin.2 hwmem hwD
  simpa [← hD] using hDle

/-- A blocked candidate is strictly inside a selected obstruction in the
only disk-level sense used here: its owned dual-face disk is a strict subset
of the selected disk. -/
def MinimalObstructionDisk.CandidateStrictlyInside
    {candidates : Finset (GridVertex m n)}
    (M : MinimalObstructionDisk (F := F) candidates)
    {v : GridVertex m n}
    (h : BlockedForcedInsertion (gridGraph m n) F v) : Prop :=
  h.obstructionDisk ⊂ M.blocked.obstructionDisk

/-- Minimality excludes a strictly contained obstruction disk for every
currently blocked candidate, in particular for one proposed to lie strictly
inside the selected disk. -/
theorem MinimalObstructionDisk.not_candidateStrictlyInside
    {candidates : Finset (GridVertex m n)}
    (M : MinimalObstructionDisk (F := F) candidates)
    {v : GridVertex m n} (hv : v ∈ candidates)
    (h : BlockedForcedInsertion (gridGraph m n) F v) :
    ¬M.CandidateStrictlyInside h := by
  intro hstrict
  exact hstrict.2 (M.minimal hv h hstrict.1)

/-- Equivalently, containment in the selected disk forces equality of disks. -/
theorem MinimalObstructionDisk.obstructionDisk_eq_of_subset
    {candidates : Finset (GridVertex m n)}
    (M : MinimalObstructionDisk (F := F) candidates)
    {v : GridVertex m n} (hv : v ∈ candidates)
    (h : BlockedForcedInsertion (gridGraph m n) F v)
    (hsub : h.obstructionDisk ⊆ M.blocked.obstructionDisk) :
    h.obstructionDisk = M.blocked.obstructionDisk :=
  Finset.Subset.antisymm hsub (M.minimal hv h hsub)

end MinimalDisk

end GridGraphs

section BoundaryArrangement

namespace SimpleGraph.CandidateOwnedClosing

variable {V : Type*} {G H : SimpleGraph V} {u v : V}

/-- Membership in the literal edge boundary of an owned closing. -/
def OnBoundary
    (C : CandidateOwnedClosing G H u) (hHG : H ≤ G)
    (edge : Sym2 V) : Prop :=
  edge ∈ (C.cycle hHG).edges

/-- A fresh owner spoke of an owned closing. -/
def IsOwnerSpoke
    (C : CandidateOwnedClosing G H u) (hHG : H ≤ G)
    (edge : Sym2 V) : Prop :=
  C.OnBoundary hHG edge ∧ edge ∉ H.edgeSet

/-- A spoke of `D` which is available off the fixed boundary `C`. -/
def HasSafeSpokeAgainst
    (D : CandidateOwnedClosing G H v) (C : CandidateOwnedClosing G H u)
    (hHG : H ≤ G) : Prop :=
  ∃ edge, D.IsOwnerSpoke hHG edge ∧ ¬C.OnBoundary hHG edge

/-- A fresh spoke of `D` which is shared with the fixed boundary `C`. -/
def BoundaryDischarge
    (D : CandidateOwnedClosing G H v) (C : CandidateOwnedClosing G H u)
    (hHG : H ≤ G) (edge : Sym2 V) : Prop :=
  D.IsOwnerSpoke hHG edge ∧ C.OnBoundary hHG edge

/-- Complete edge-level arrangement classification.  Grid edges do not have
an additional transverse-crossing case: away from a shared literal edge, the
owned-closing theorem leaves an old path edge or an owner-incident spoke. -/
theorem boundary_arrangement
    (D : CandidateOwnedClosing G H v) (C : CandidateOwnedClosing G H u)
    (hHG : H ≤ G) {edge : Sym2 V} (hedge : D.OnBoundary hHG edge) :
    (D.OnBoundary hHG edge ∧ C.OnBoundary hHG edge) ∨
      (edge ∈ H.edgeSet ∧ ¬C.OnBoundary hHG edge) ∨
      (v ∈ edge ∧ ¬C.OnBoundary hHG edge) := by
  by_cases hshared : C.OnBoundary hHG edge
  · exact Or.inl ⟨hedge, hshared⟩
  · rcases D.edge_mem_old_or_incident hHG hedge with hold | howner
    · exact Or.inr (Or.inl ⟨hold, hshared⟩)
    · exact Or.inr (Or.inr ⟨howner, hshared⟩)

/-- Every fresh boundary edge of the second closing is either a safe spoke or
a discharge onto the first boundary. -/
theorem safeSpoke_or_boundaryDischarge
    (D : CandidateOwnedClosing G H v) (C : CandidateOwnedClosing G H u)
    (hHG : H ≤ G) {edge : Sym2 V} (hspoke : D.IsOwnerSpoke hHG edge) :
    (D.IsOwnerSpoke hHG edge ∧ ¬C.OnBoundary hHG edge) ∨
      D.BoundaryDischarge C hHG edge := by
  by_cases hboundary : C.OnBoundary hHG edge
  · exact Or.inr ⟨hspoke, hboundary⟩
  · exact Or.inl ⟨hspoke, hboundary⟩

/-- Ownership sharpens the preceding alternative: every fresh boundary edge
is incident to the owner of the second closing. -/
theorem owner_mem_of_isOwnerSpoke
    (D : CandidateOwnedClosing G H v) (hHG : H ≤ G)
    {edge : Sym2 V} (hspoke : D.IsOwnerSpoke hHG edge) :
    v ∈ edge := by
  rcases D.edge_mem_old_or_incident hHG hspoke.1 with hold | howner
  · exact (hspoke.2 hold).elim
  · exact howner

/-- The strongest unconditional repair/discharge alternative for an owned
closing.  A one-spoke closing either has a safe spoke or one unique discharge;
a two-spoke closing either has a safe spoke or its two distinct spokes both
discharge onto the fixed boundary. -/
theorem safeSpoke_or_discharge_classification
    (D : CandidateOwnedClosing G H v) (C : CandidateOwnedClosing G H u)
    (hHG : H ≤ G) :
    D.HasSafeSpokeAgainst C hHG ∨
      (∃! edge, D.BoundaryDischarge C hHG edge) ∨
      (∃ edge₁ edge₂, edge₁ ≠ edge₂ ∧
        D.BoundaryDischarge C hHG edge₁ ∧
        D.BoundaryDischarge C hHG edge₂ ∧
        ∀ edge, D.IsOwnerSpoke hHG edge → edge = edge₁ ∨ edge = edge₂) := by
  classical
  cases D with
  | one w hvw hfresh p hp =>
      let spoke : Sym2 V := s(v, w)
      have hspoke :
          (CandidateOwnedClosing.one w hvw hfresh p hp).IsOwnerSpoke hHG spoke := by
        refine ⟨?_, hfresh⟩
        simp [CandidateOwnedClosing.OnBoundary, CandidateOwnedClosing.cycle, spoke]
      rcases (CandidateOwnedClosing.one w hvw hfresh p hp).safeSpoke_or_boundaryDischarge
          C hHG hspoke with hsafe | hdischarge
      · exact Or.inl ⟨spoke, hsafe⟩
      · refine Or.inr (Or.inl ⟨spoke, hdischarge, ?_⟩)
        intro edge hedge
        rcases hedge.1 with ⟨hedgeCycle, hedgeFresh⟩
        simp only [CandidateOwnedClosing.OnBoundary, CandidateOwnedClosing.cycle,
          Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse] at hedgeCycle
        rcases hedgeCycle with rfl | hedgePath
        · rfl
        · have hedgePath' : edge ∈ p.edges := by
            simpa [Walk.edges_map] using hedgePath
          exact (hedgeFresh (p.edges_subset_edgeSet hedgePath')).elim
  | two a b hab hva hvb hfresha hfreshb p hp hvnot =>
      let spoke₁ : Sym2 V := s(v, a)
      let spoke₂ : Sym2 V := s(v, b)
      have hspoke₁ : IsOwnerSpoke
          (CandidateOwnedClosing.two a b hab hva hvb hfresha hfreshb p hp hvnot)
          hHG spoke₁ := by
        refine ⟨?_, hfresha⟩
        simp [CandidateOwnedClosing.OnBoundary, CandidateOwnedClosing.cycle, spoke₁]
      have hspoke₂ : IsOwnerSpoke
          (CandidateOwnedClosing.two a b hab hva hvb hfresha hfreshb p hp hvnot)
          hHG spoke₂ := by
        refine ⟨?_, hfreshb⟩
        simp [CandidateOwnedClosing.OnBoundary, CandidateOwnedClosing.cycle, spoke₂]
      by_cases hsafe₁ : ¬C.OnBoundary hHG spoke₁
      · exact Or.inl ⟨spoke₁, hspoke₁, hsafe₁⟩
      by_cases hsafe₂ : ¬C.OnBoundary hHG spoke₂
      · exact Or.inl ⟨spoke₂, hspoke₂, hsafe₂⟩
      · refine Or.inr (Or.inr ⟨spoke₁, spoke₂, ?_,
          ⟨hspoke₁, not_not.mp hsafe₁⟩, ⟨hspoke₂, not_not.mp hsafe₂⟩, ?_⟩)
        · intro heq
          have : a = b := by
            rcases (by simpa [spoke₁, spoke₂] using heq) with hab' | ⟨hvb', hav'⟩
            · exact hab'
            · exact (hva.ne hav'.symm).elim
          exact hab this
        · intro edge hedge
          rcases hedge with ⟨hedgeCycle, hedgeFresh⟩
          simp only [CandidateOwnedClosing.OnBoundary, CandidateOwnedClosing.cycle,
            Walk.edges_cons, Walk.edges_concat, List.mem_cons] at hedgeCycle
          simp at hedgeCycle
          rcases hedgeCycle with rfl | hedgePath | rfl
          · exact Or.inl rfl
          · have hedgePath' : edge ∈ p.edges := by
              simpa [Walk.edges_map] using hedgePath
            exact (hedgeFresh (p.edges_subset_edgeSet hedgePath')).elim
          · exact Or.inr (by simp [spoke₂])

end SimpleGraph.CandidateOwnedClosing

end BoundaryArrangement

namespace GridGraphs

open Finset SimpleGraph

section MinimalBoundaryArrangement

variable {m n : Nat} {F : Set (GridVertex m n)}
  {candidates : Finset (GridVertex m n)}

/-- Specialization of the edge arrangement classification to the canonical
boundary of a selected minimal obstruction disk. -/
theorem MinimalObstructionDisk.canonical_boundary_arrangement
    (M : MinimalObstructionDisk (F := F) candidates)
    {v : GridVertex m n}
    (h : BlockedForcedInsertion (gridGraph m n) F v)
    {edge : Sym2 (GridVertex m n)}
    (hedge : h.canonicalClosing.OnBoundary
      (forcedEdgeGraph_le (gridGraph m n) F) edge) :
    (h.canonicalClosing.OnBoundary
        (forcedEdgeGraph_le (gridGraph m n) F) edge ∧
      M.blocked.canonicalClosing.OnBoundary
        (forcedEdgeGraph_le (gridGraph m n) F) edge) ∨
      (edge ∈ (forcedEdgeGraph (gridGraph m n) F).edgeSet ∧
        ¬M.blocked.canonicalClosing.OnBoundary
          (forcedEdgeGraph_le (gridGraph m n) F) edge) ∨
      (v ∈ edge ∧ ¬M.blocked.canonicalClosing.OnBoundary
        (forcedEdgeGraph_le (gridGraph m n) F) edge) :=
  h.canonicalClosing.boundary_arrangement M.blocked.canonicalClosing
    (forcedEdgeGraph_le (gridGraph m n) F) hedge

/-- The old paths of a blocked candidate and the selected obstruction meet in
a connected forest subpath whenever two common vertices are specified. -/
theorem MinimalObstructionDisk.canonical_oldPath_intersection_connected
    (M : MinimalObstructionDisk (F := F) candidates)
    {v x y : GridVertex m n}
    (h : BlockedForcedInsertion (gridGraph m n) F v)
    (hxM : x ∈ M.blocked.canonicalClosing.oldPathSupport)
    (hxv : x ∈ h.canonicalClosing.oldPathSupport)
    (hyM : y ∈ M.blocked.canonicalClosing.oldPathSupport)
    (hyv : y ∈ h.canonicalClosing.oldPathSupport) :
    ∃ r : (forcedEdgeGraph (gridGraph m n) F).Walk x y,
      r.IsPath ∧ ∀ z ∈ r.support,
        z ∈ M.blocked.canonicalClosing.oldPathSupport ∧
          z ∈ h.canonicalClosing.oldPathSupport :=
  CandidateOwnedClosing.oldPathSupport_intersection_connected
    M.blocked.currentForest M.blocked.canonicalClosing h.canonicalClosing
      hxM hxv hyM hyv

/-- Canonical safe-repair/boundary-discharge alternative at a selected
minimal obstruction.  This does not assert that the disks are globally
laminar or that an off-boundary spoke alone completes a global repair. -/
theorem MinimalObstructionDisk.canonical_safeSpoke_or_discharge
    (M : MinimalObstructionDisk (F := F) candidates)
    {v : GridVertex m n}
    (h : BlockedForcedInsertion (gridGraph m n) F v) :
    h.canonicalClosing.HasSafeSpokeAgainst M.blocked.canonicalClosing
        (forcedEdgeGraph_le (gridGraph m n) F) ∨
      (∃! edge, h.canonicalClosing.BoundaryDischarge
        M.blocked.canonicalClosing
        (forcedEdgeGraph_le (gridGraph m n) F) edge) ∨
      (∃ edge₁ edge₂, edge₁ ≠ edge₂ ∧
        h.canonicalClosing.BoundaryDischarge M.blocked.canonicalClosing
          (forcedEdgeGraph_le (gridGraph m n) F) edge₁ ∧
        h.canonicalClosing.BoundaryDischarge M.blocked.canonicalClosing
          (forcedEdgeGraph_le (gridGraph m n) F) edge₂ ∧
        ∀ edge, h.canonicalClosing.IsOwnerSpoke
          (forcedEdgeGraph_le (gridGraph m n) F) edge →
            edge = edge₁ ∨ edge = edge₂) :=
  h.canonicalClosing.safeSpoke_or_discharge_classification
    M.blocked.canonicalClosing (forcedEdgeGraph_le (gridGraph m n) F)

end MinimalBoundaryArrangement

end GridGraphs
