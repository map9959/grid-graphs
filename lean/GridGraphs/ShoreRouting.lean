import GridGraphs.GeometricContourMarks

/-!
# Fundamental-shore marks-or-ports routing

Lane demand in a tree shore is routed into the disjoint sum of internal
geometric waste marks and edge-labelled outgoing cotree ports. The exact
existence criterion is recorded in both resource and cut-edge form.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- An injective routing of `k` lanes into internal marks or distinct outgoing
cotree ports of one fundamental shore. -/
def FundamentalShoreLaneRouting {m n k : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (d : GridDirectionalDart T) :=
  Fin k ↪ FundamentalShoreResource hTgrid hdegree d

/-- Local routing exists exactly when marks plus outgoing ports cover the lane
demand. No marks-only Hall claim is assumed. -/
theorem nonempty_fundamentalShoreLaneRouting_iff
    {m n k : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (d : GridDirectionalDart T) :
    Nonempty (FundamentalShoreLaneRouting (k := k) hTgrid hdegree d) ↔
      k ≤ (GeometricCotreeContourMark.inVertices
        (T := T) (hTgrid := hTgrid) (hdegree := hdegree)
        d.targetShoreVertices).card + d.cotreePorts.card := by
  unfold FundamentalShoreLaneRouting
  rw [Function.Embedding.nonempty_iff_card_le]
  simp only [Fintype.card_fin, card_fundamentalShoreResource]

/-- Cut form of the same criterion: the attachment occupies exactly one cut
edge, while all remaining cut capacity is available as cotree ports. -/
theorem nonempty_fundamentalShoreLaneRouting_iff_add_one_le_marks_add_cut
    {m n k : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    (hdegree : ∀ v, 1 ≤ T.degree v) (d : GridDirectionalDart T) :
    Nonempty (FundamentalShoreLaneRouting (k := k) hTgrid hdegree d) ↔
      k + 1 ≤ (GeometricCotreeContourMark.inVertices
        (T := T) (hTgrid := hTgrid) (hdegree := hdegree)
        d.targetShoreVertices).card + d.shoreCrossingEdges.card := by
  rw [nonempty_fundamentalShoreLaneRouting_iff]
  rw [d.card_shoreCrossingEdges_eq_card_cotreePorts_add_one hTgrid hacyc]
  omega

/-- Distinct lanes routed through ports use distinct edge labels, including
parallel boundary incidences represented by different `GridEdge` values. -/
theorem port_eq_of_fundamentalShoreLaneRouting
    {m n k : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    {hTgrid : T ≤ gridGraph m n} {hdegree : ∀ v, 1 ≤ T.degree v}
    {d : GridDirectionalDart T}
    (routing : FundamentalShoreLaneRouting (k := k) hTgrid hdegree d)
    {i j : Fin k} {pi pj : ↥d.cotreePorts}
    (hi : routing.toFun i = Sum.inr pi) (hj : routing.toFun j = Sum.inr pj)
    (hport : pi = pj) : i = j := by
  unfold FundamentalShoreLaneRouting at routing
  apply routing.injective
  change routing.toFun i = routing.toFun j
  rw [hi, hj, hport]

/-- Discharge every outgoing port into a distinct mark outside the shore. The
internal/external location split makes the combined resource map injective. -/
noncomputable def fundamentalShoreResourceDischarge
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    {hTgrid : T ≤ gridGraph m n} {hdegree : ∀ v, 1 ≤ T.degree v}
    {d : GridDirectionalDart T}
    (portMark : ↥d.cotreePorts ↪
      GeometricCotreeContourMark T hTgrid hdegree)
    (portMark_outside : ∀ p,
      (portMark.toFun p).vertex ∉ d.targetShoreVertices) :
    FundamentalShoreResource hTgrid hdegree d ↪
      GeometricCotreeContourMark T hTgrid hdegree where
  toFun resource :=
    match resource with
    | Sum.inl mark => mark.1
    | Sum.inr port => portMark.toFun port
  inj' := by
    intro a b hab
    rcases a with mark | port <;> rcases b with mark' | port'
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact hab
    · have hinside :=
        (GeometricCotreeContourMark.mem_inVertices
          d.targetShoreVertices mark.1).1 mark.2
      have hv := congrArg GeometricCotreeContourMark.vertex hab
      have hportInside : (portMark.toFun port').vertex ∈
          d.targetShoreVertices := by
        simpa only using hv ▸ hinside
      exact (portMark_outside port' hportInside).elim
    · have hinside :=
        (GeometricCotreeContourMark.mem_inVertices
          d.targetShoreVertices mark'.1).1 mark'.2
      have hv := congrArg GeometricCotreeContourMark.vertex hab
      have hportInside : (portMark.toFun port).vertex ∈
          d.targetShoreVertices := by
        simpa only using hv.symm ▸ hinside
      exact (portMark_outside port hportInside).elim
    · apply congrArg Sum.inr
      exact portMark.injective hab

/-- One local lane routing becomes a genuine marking after its outgoing
channels have an injective external discharge. -/
noncomputable def dischargeFundamentalShoreLaneRouting
    {m n k : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    {hTgrid : T ≤ gridGraph m n} {hdegree : ∀ v, 1 ≤ T.degree v}
    {d : GridDirectionalDart T}
    (routing : FundamentalShoreLaneRouting (k := k) hTgrid hdegree d)
    (portMark : ↥d.cotreePorts ↪
      GeometricCotreeContourMark T hTgrid hdegree)
    (portMark_outside : ∀ p,
      (portMark.toFun p).vertex ∉ d.targetShoreVertices) :
    Fin k ↪ GeometricCotreeContourMark T hTgrid hdegree :=
  routing.trans
    (fundamentalShoreResourceDischarge portMark portMark_outside)

end GridGraphs
