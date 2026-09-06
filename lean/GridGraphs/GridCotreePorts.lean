import GridGraphs.TreeContour

/-!
# Edge-labelled cotree ports of fundamental tree shores

A fundamental shore of a tree has exactly one tree edge crossing its boundary:
the attachment edge. Every other ambient grid edge crossing that shore is an
omitted edge and therefore a cotree transport port.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

namespace GridEdge

/-- An edge has one endpoint in `S` and the other outside. -/
def Crosses {m n : Nat} (S : Finset (GridVertex m n)) (e : GridEdge m n) : Prop :=
  (e.primalEndpoints.1 ∈ S ∧ e.primalEndpoints.2 ∉ S) ∨
    (e.primalEndpoints.2 ∈ S ∧ e.primalEndpoints.1 ∉ S)

end GridEdge

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- The coordinate edge underlying a directional tree dart. -/
noncomputable def coordinateEdge (hTgrid : T ≤ gridGraph m n)
    (d : GridDirectionalDart T) : GridEdge m n :=
  (GridEdge.equivGridGraphEdgeSet m n).symm
    ⟨d.edgeSym2, by
      change s(d.source, d.target) ∈ (gridGraph m n).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hTgrid d.adj⟩

omit [DecidableRel T.Adj] in
@[simp] theorem coordinateEdge_primalSym2 (hTgrid : T ≤ gridGraph m n)
    (d : GridDirectionalDart T) :
    (d.coordinateEdge hTgrid).primalSym2 = d.edgeSym2 := by
  have h := (GridEdge.equivGridGraphEdgeSet m n).apply_symm_apply
    ⟨d.edgeSym2, by
      change s(d.source, d.target) ∈ (gridGraph m n).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hTgrid d.adj⟩
  exact congrArg Subtype.val h

/-- Omitted grid edges crossing the target shore of `d`. -/
noncomputable def cotreePorts (d : GridDirectionalDart T) : Finset (GridEdge m n) :=
  by
    classical
    exact Finset.univ.filter fun e =>
      e.Crosses d.targetShoreVertices ∧
        ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2

@[simp] theorem mem_cotreePorts (d : GridDirectionalDart T) (e : GridEdge m n) :
    e ∈ d.cotreePorts ↔
      e.Crosses d.targetShoreVertices ∧
        ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
  simp [cotreePorts]

/-- All ambient coordinate edges crossing the target shore. -/
noncomputable def shoreCrossingEdges (d : GridDirectionalDart T) :
    Finset (GridEdge m n) := by
  classical
  exact Finset.univ.filter fun e => e.Crosses d.targetShoreVertices

@[simp] theorem mem_shoreCrossingEdges (d : GridDirectionalDart T)
    (e : GridEdge m n) :
    e ∈ d.shoreCrossingEdges ↔ e.Crosses d.targetShoreVertices := by
  simp [shoreCrossingEdges]

private theorem crosses_of_primalSym2_eq_edgeSym2
    (hacyc : T.IsAcyclic) (d : GridDirectionalDart T) (e : GridEdge m n)
    (he : e.primalSym2 = d.edgeSym2) :
    e.Crosses d.targetShoreVertices := by
  rw [GridEdge.Crosses]
  rw [GridEdge.primalSym2, edgeSym2, Sym2.eq_iff] at he
  have htarget := target_mem_targetShoreVertices d
  have hsource := source_notMem_targetShoreVertices hacyc d
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · right
    rw [h₁, h₂]
    exact ⟨htarget, hsource⟩
  · left
    rw [h₁, h₂]
    exact ⟨htarget, hsource⟩

/-- Exact cut decomposition: a grid edge crosses a fundamental tree shore iff
it is the attachment tree edge or an omitted cotree port. -/
theorem crosses_targetShore_iff_eq_coordinateEdge_or_mem_cotreePorts
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    (d : GridDirectionalDart T) (e : GridEdge m n) :
    e.Crosses d.targetShoreVertices ↔
      e = d.coordinateEdge hTgrid ∨ e ∈ d.cotreePorts := by
  constructor
  · intro hcross
    by_cases heT : T.Adj e.primalEndpoints.1 e.primalEndpoints.2
    · obtain ⟨x, hxSource, hxTarget⟩ := exists_of_adj hTgrid heT
      have heq : x.edgeSym2 = d.edgeSym2 := by
        rcases hcross with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
        · apply edgeSym2_eq_of_source_mem_target_notMem d x
            (by simpa only [hxSource] using h₁)
            (by simpa only [hxTarget] using h₂)
        · have hrev := edgeSym2_eq_of_source_mem_target_notMem d x.reverse
            (by simpa [reverse, hxTarget] using h₂)
            (by simpa [reverse, hxSource] using h₁)
          calc
            x.edgeSym2 = x.reverse.edgeSym2 := by
              simp only [edgeSym2, reverse, Sym2.eq_swap]
            _ = d.edgeSym2 := hrev
      left
      apply GridEdge.primalSym2_injective
      rw [coordinateEdge_primalSym2]
      calc
        e.primalSym2 = x.edgeSym2 := by
          simp only [GridEdge.primalSym2, edgeSym2, hxSource, hxTarget]
        _ = d.edgeSym2 := heq
    · exact Or.inr ((mem_cotreePorts d e).2 ⟨hcross, heT⟩)
  · rintro (rfl | hport)
    · apply crosses_of_primalSym2_eq_edgeSym2 hacyc
      exact coordinateEdge_primalSym2 hTgrid d
    · exact (mem_cotreePorts d e).1 hport |>.1

/-- The attachment edge is not a cotree port. -/
theorem coordinateEdge_notMem_cotreePorts
    (hTgrid : T ≤ gridGraph m n) (d : GridDirectionalDart T) :
    d.coordinateEdge hTgrid ∉ d.cotreePorts := by
  rw [mem_cotreePorts]
  push Not
  intro _
  have hsym := coordinateEdge_primalSym2 hTgrid d
  rw [GridEdge.primalSym2, edgeSym2, Sym2.eq_iff] at hsym
  rcases hsym with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simpa [h₁, h₂] using d.adj
  · simpa [h₁, h₂] using d.adj.symm

/-- Set-level form of the exact fundamental cut decomposition. -/
theorem shoreCrossingEdges_eq_insert_coordinateEdge_cotreePorts
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    (d : GridDirectionalDart T) :
    d.shoreCrossingEdges = insert (d.coordinateEdge hTgrid) d.cotreePorts := by
  classical
  ext e
  rw [mem_shoreCrossingEdges]
  simp only [Finset.mem_insert]
  exact crosses_targetShore_iff_eq_coordinateEdge_or_mem_cotreePorts
    hTgrid hacyc d e

/-- A fundamental shore has one attachment edge in addition to all its cotree
ports, preserving edge labels and boundary multiplicity. -/
theorem card_shoreCrossingEdges_eq_card_cotreePorts_add_one
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    (d : GridDirectionalDart T) :
    d.shoreCrossingEdges.card = d.cotreePorts.card + 1 := by
  rw [shoreCrossingEdges_eq_insert_coordinateEdge_cotreePorts hTgrid hacyc]
  rw [Finset.card_insert_of_notMem (coordinateEdge_notMem_cotreePorts hTgrid d)]

/-- Occurrences of one labelled cotree edge are convex along a nested chain of
fundamental shores. Thus repeated occurrences are one continuing channel, not
independent local capacity. -/
theorem mem_cotreePorts_of_nested
    {a b c : GridDirectionalDart T}
    (hab : a.targetShoreVertices ⊆ b.targetShoreVertices)
    (hbc : b.targetShoreVertices ⊆ c.targetShoreVertices)
    {e : GridEdge m n} (ha : e ∈ a.cotreePorts) (hc : e ∈ c.cotreePorts) :
    e ∈ b.cotreePorts := by
  rw [mem_cotreePorts] at ha hc ⊢
  refine ⟨?_, ha.2⟩
  rcases ha.1 with ⟨haIn, haOut⟩ | ⟨haIn, haOut⟩
  · left
    refine ⟨hab haIn, ?_⟩
    intro he₂b
    have he₂c := hbc he₂b
    rcases hc.1 with hc | hc
    · exact hc.2 he₂c
    · exact hc.2 (hbc (hab haIn))
  · right
    refine ⟨hab haIn, ?_⟩
    intro he₁b
    have he₁c := hbc he₁b
    rcases hc.1 with hc | hc
    · exact hc.2 (hbc (hab haIn))
    · exact hc.2 he₁c

end GridDirectionalDart

end GridGraphs
