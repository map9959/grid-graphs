import GridGraphs.Geometry.ContourMarks
import GridGraphs.Geometry.GridCotreePorts

/-!
# Geometric realization of contour return marks

The abstract `T.degree v - 1` return ledger is realized by all outgoing contour
darts at `v` except one base visit. Thus every return mark now has an actual
location on the global tree contour.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Contour darts whose visit starts at `v`. -/
def SourceDartAt {m n : Nat} (T : SimpleGraph (GridVertex m n))
    (v : GridVertex m n) :=
  {d : GridDirectionalDart T // d.source = v}

noncomputable instance {m n : Nat} (T : SimpleGraph (GridVertex m n))
    [DecidableRel T.Adj] (v : GridVertex m n) : Fintype (SourceDartAt T v) :=
  by
    unfold SourceDartAt
    infer_instance

noncomputable instance {m n : Nat} (T : SimpleGraph (GridVertex m n))
    (v : GridVertex m n) : DecidableEq (SourceDartAt T v) :=
  Classical.decEq _

namespace SourceDartAt

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- A source dart is equivalently one tree neighbor of its source vertex. -/
noncomputable def equivNeighbor (hTgrid : T ≤ gridGraph m n)
    (v : GridVertex m n) :
    SourceDartAt T v ≃ ↥(T.neighborFinset v) := by
  let f : SourceDartAt T v → ↥(T.neighborFinset v) := fun d =>
    ⟨d.1.target, by
      rw [SimpleGraph.mem_neighborFinset]
      simpa only [d.2] using d.1.adj⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply GridDirectionalDart.ext_endpoints
    · exact a.2.trans b.2.symm
    · exact congrArg Subtype.val hab
  · intro w
    obtain ⟨d, hdSource, hdTarget⟩ :=
      GridDirectionalDart.exists_of_adj hTgrid
        (by simpa only [SimpleGraph.mem_neighborFinset] using w.2)
    refine ⟨⟨d, hdSource⟩, ?_⟩
    apply Subtype.ext
    exact hdTarget

theorem card_eq_degree (hTgrid : T ≤ gridGraph m n)
    (v : GridVertex m n) :
    Fintype.card (SourceDartAt T v) = T.degree v := by
  rw [Fintype.card_congr (equivNeighbor hTgrid v)]
  simp only [Fintype.card_coe, SimpleGraph.degree]

end SourceDartAt

/-- A chosen first contour visit at `v`. All other visits are return marks. -/
noncomputable def baseSourceDart {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (v : GridVertex m n) : SourceDartAt T v := by
  have hcard : 0 < Fintype.card (SourceDartAt T v) := by
    rw [SourceDartAt.card_eq_degree hTgrid]
    exact hdegree v
  exact Fintype.card_pos_iff.mp hcard |>.some

/-- A geometrically located return: an outgoing contour dart other than the
chosen first visit at its source. -/
def ReturnDartAt {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    [DecidableRel T.Adj] (hTgrid : T ≤ gridGraph m n)
    (hdegree : ∀ v, 1 ≤ T.degree v) (v : GridVertex m n) :=
  ↥((Finset.univ : Finset (SourceDartAt T v)).erase
    (baseSourceDart hTgrid hdegree v))

noncomputable instance {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    [DecidableRel T.Adj] (hTgrid : T ≤ gridGraph m n)
    (hdegree : ∀ v, 1 ≤ T.degree v) (v : GridVertex m n) :
    Fintype (ReturnDartAt hTgrid hdegree v) :=
  by
    classical
    unfold ReturnDartAt
    infer_instance

theorem card_returnDartAt {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    [DecidableRel T.Adj] (hTgrid : T ≤ gridGraph m n)
    (hdegree : ∀ v, 1 ≤ T.degree v) (v : GridVertex m n) :
    Fintype.card (ReturnDartAt hTgrid hdegree v) = T.degree v - 1 := by
  classical
  rw [show Fintype.card (ReturnDartAt hTgrid hdegree v) =
      ((Finset.univ : Finset (SourceDartAt T v)).erase
        (baseSourceDart hTgrid hdegree v)).card by
    let e : ReturnDartAt hTgrid hdegree v ≃
        ↥((Finset.univ : Finset (SourceDartAt T v)).erase
          (baseSourceDart hTgrid hdegree v)) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => by cases x; rfl }
    rw [Fintype.card_congr e, Fintype.card_coe]]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simpa only [Finset.card_univ] using
    congrArg (fun k => k - 1) (SourceDartAt.card_eq_degree hTgrid v)

/-- Waste marks with return marks realized as actual contour darts. Exterior
sectors retain their local boundary-sector index. -/
def GeometricCotreeContourMark {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v) :=
  let U := supportFinset (gridGraph m n \ T)
  (Σ v : ↥U, Fin (gridBoundaryDeficiency m n v.1)) ⊕
    (Σ v : ↥U, ReturnDartAt hTgrid hdegree v.1)

noncomputable instance {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v) :
    Fintype (GeometricCotreeContourMark T hTgrid hdegree) := by
  unfold GeometricCotreeContourMark
  infer_instance

/-- Geometric and abstract marks are equinumerous. -/
theorem card_geometricCotreeContourMark_eq_card_abstract {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v) :
    Fintype.card (GeometricCotreeContourMark T hTgrid hdegree) =
      Fintype.card (CotreeContourMark T) := by
  let U := supportFinset (gridGraph m n \ T)
  change Fintype.card
      ((Σ v : ↥U, Fin (gridBoundaryDeficiency m n v.1)) ⊕
        (Σ v : ↥U, ReturnDartAt hTgrid hdegree v.1)) =
    Fintype.card
      ((Σ v : ↥U, Fin (gridBoundaryDeficiency m n v.1)) ⊕
        (Σ v : ↥U, Fin (T.degree v.1 - 1)))
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact card_returnDartAt hTgrid hdegree v

/-- A noncomputable equivalence lets later routing target geometric marks while
reusing the exact abstract waste-cardinality theorem. -/
noncomputable def geometricCotreeContourMarkEquiv {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v) :
    GeometricCotreeContourMark T hTgrid hdegree ≃ CotreeContourMark T :=
  Fintype.equivOfCardEq
    (card_geometricCotreeContourMark_eq_card_abstract T hTgrid hdegree)

/-- For a spanning grid tree, geometric marks realize incidence waste exactly. -/
theorem card_geometricCotreeContourMark_eq_incidenceWaste
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (GeometricCotreeContourMark T hT.le
      (fun v => tree_degree_pos (by nlinarith) hT v)) =
        incidenceWaste (gridGraph m n \ T) := by
  rw [card_geometricCotreeContourMark_eq_card_abstract]
  exact card_cotreeContourMark_eq_incidenceWaste hm hn hT

/-- Geometric version of the transverse certificate. -/
def GeometricTransverseContourMarking {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T) :=
  Fin n ↪ GeometricCotreeContourMark T hT.le
    (fun v => tree_degree_pos (by nlinarith [hn]) hT v)

/-- A geometric transverse injection proves the weak linear waste bound. -/
theorem n_le_incidenceWaste_of_geometricTransverseContourMarking
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (marking : GeometricTransverseContourMarking hn hT) :
    n ≤ incidenceWaste (gridGraph n n \ T) := by
  have hcard := Fintype.card_le_of_injective marking.toFun marking.injective
  rw [Fintype.card_fin,
    card_geometricCotreeContourMark_eq_incidenceWaste hn hn hT] at hcard
  exact hcard

namespace GeometricCotreeContourMark

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
  {hTgrid : T ≤ gridGraph m n} {hdegree : ∀ v, 1 ≤ T.degree v}

/-- Vertex at which a geometric mark occurs. -/
def vertex : GeometricCotreeContourMark T hTgrid hdegree → GridVertex m n
  | Sum.inl mark => mark.1.1
  | Sum.inr mark => mark.1.1

/-- A return mark carries an actual contour dart; an exterior mark does not. -/
def returnDart? : GeometricCotreeContourMark T hTgrid hdegree →
    Option (GridDirectionalDart T)
  | Sum.inl _ => none
  | Sum.inr mark => some mark.2.1.1

theorem returnDart?_source {mark : GeometricCotreeContourMark T hTgrid hdegree}
    {d : GridDirectionalDart T} (hmark : mark.returnDart? = some d) :
    d.source = mark.vertex := by
  rcases mark with mark | mark
  · simp [returnDart?] at hmark
  · simp only [returnDart?, Option.some.injEq] at hmark
    subst d
    exact mark.2.1.2

/-- Geometric marks located in a specified vertex set. -/
noncomputable def inVertices (S : Finset (GridVertex m n)) :
    Finset (GeometricCotreeContourMark T hTgrid hdegree) :=
  Finset.univ.filter fun mark => mark.vertex ∈ S

@[simp] theorem mem_inVertices (S : Finset (GridVertex m n))
    (mark : GeometricCotreeContourMark T hTgrid hdegree) :
    mark ∈ inVertices S ↔ mark.vertex ∈ S := by
  simp [inVertices]

end GeometricCotreeContourMark

/-- Local routing resources of a fundamental shore: waste marks physically
inside the shore and distinct omitted edges crossing out of it. -/
def FundamentalShoreResource {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (d : GridDirectionalDart T) :=
  ↥(GeometricCotreeContourMark.inVertices
      (T := T) (hTgrid := hTgrid) (hdegree := hdegree)
      d.targetShoreVertices) ⊕ ↥d.cotreePorts

noncomputable instance {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (d : GridDirectionalDart T) :
    Fintype (FundamentalShoreResource hTgrid hdegree d) := by
  unfold FundamentalShoreResource
  infer_instance

theorem card_fundamentalShoreResource {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hdegree : ∀ v, 1 ≤ T.degree v)
    (d : GridDirectionalDart T) :
    Fintype.card (FundamentalShoreResource hTgrid hdegree d) =
      (GeometricCotreeContourMark.inVertices
        (T := T) (hTgrid := hTgrid) (hdegree := hdegree)
        d.targetShoreVertices).card + d.cotreePorts.card := by
  unfold FundamentalShoreResource
  rw [Fintype.card_sum]
  simp only [Fintype.card_coe]

/-- Exact local interface ledger. The shore's routing capacity plus its one
tree attachment is its internal marks plus every ambient cut edge. This is the
composable replacement for the false marks-only shore bound. -/
theorem card_fundamentalShoreResource_add_one
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    (hdegree : ∀ v, 1 ≤ T.degree v) (d : GridDirectionalDart T) :
    Fintype.card (FundamentalShoreResource hTgrid hdegree d) + 1 =
      (GeometricCotreeContourMark.inVertices
        (T := T) (hTgrid := hTgrid) (hdegree := hdegree)
        d.targetShoreVertices).card + d.shoreCrossingEdges.card := by
  rw [card_fundamentalShoreResource]
  rw [d.card_shoreCrossingEdges_eq_card_cotreePorts_add_one hTgrid hacyc]
  omega

end GridGraphs
