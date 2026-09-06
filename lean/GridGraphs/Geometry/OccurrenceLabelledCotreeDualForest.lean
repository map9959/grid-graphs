import Mathlib.Combinatorics.SimpleGraph.Metric
import GridGraphs.Geometry.BareCombTransition
import GridGraphs.Geometry.GridDual
import GridGraphs.Geometry.GridCotreeSplitOuter
import GridGraphs.Geometry.GridExpandedContour
import GridGraphs.Forests.PlaneChannelForest

/-!
# Occurrence-labelled cotree-dual forests

The face dual of a grid is a simple graph and therefore cannot itself retain
parallel outer incidences.  Here every omitted-edge occurrence gets its own
edge vertex.  Equal `GridEdge` labels consequently remain distinct until they
meet at a common face vertex.

The core incidence graph is oriented by shortest distance to `GridFace.out`.
Vertices in components not reaching `out` are left as roots; no boundary-exit
or physical-resource assertion is hidden in the construction.  A private leaf
is then attached to every occurrence, giving an unconditional start-leaf
embedding for later inward-collision instantiations.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- The barycentric core: one vertex for every labelled occurrence and one for
every grid face.  The occurrence summand prevents equal coordinate transitions
from being identified. -/
def OccurrenceCotreeDualCore (O : Type*) := O ⊕ GridFace m n

namespace OccurrenceCotreeDualCore

variable {O : Type*} (transition : O → LabelledCotreeTransition T)

noncomputable instance coreFintype [Fintype O] :
    Fintype (OccurrenceCotreeDualCore (m := m) (n := n) O) := by
  unfold OccurrenceCotreeDualCore
  infer_instance

noncomputable instance coreDecidableEq [DecidableEq O] :
    DecidableEq (OccurrenceCotreeDualCore (m := m) (n := n) O) := by
  unfold OccurrenceCotreeDualCore
  infer_instance

/-- A face is incident to the labelled omitted edge carried by an occurrence. -/
def Incident (o : O) (f : GridFace m n) : Prop :=
  f = (transition o).1.dualEndpoints.1 ∨
    f = (transition o).1.dualEndpoints.2

/-- Barycentric incidence graph of occurrence-labelled omitted edges. -/
def graph : SimpleGraph (OccurrenceCotreeDualCore (m := m) (n := n) O) where
  Adj
    | .inl o, .inr f => Incident transition o f
    | .inr f, .inl o => Incident transition o f
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless := by
    intro x h
    cases x <;> simp_all

noncomputable instance graphDecidableRel [DecidableEq O] :
    DecidableRel (graph transition).Adj := by
  classical
  intro x y
  infer_instance

/-- The unsplit outer face used only as a distance target.  Edge occurrences
remain split even though their paths may terminate at this common face. -/
def outer : OccurrenceCotreeDualCore (m := m) (n := n) O := .inr GridFace.out

theorem edge_incident_fst (o : O) :
    (graph transition).Adj (.inl o) (.inr (transition o).1.dualEndpoints.1) :=
  Or.inl rfl

theorem edge_incident_snd (o : O) :
    (graph transition).Adj (.inl o) (.inr (transition o).1.dualEndpoints.2) :=
  Or.inr rfl

/-- A boundary occurrence is adjacent to the unsplit outer face.  Thus an
endpoint equal to `out` does not by itself determine a fresh split outer port. -/
theorem edge_incident_outer_of_fst_eq (o : O)
    (h : (transition o).1.dualEndpoints.1 = GridFace.out) :
    (graph transition).Adj (.inl o) outer := by
  simpa [outer, h] using edge_incident_fst transition o

/-- The symmetric endpoint-side version of `edge_incident_outer_of_fst_eq`. -/
theorem edge_incident_outer_of_snd_eq (o : O)
    (h : (transition o).1.dualEndpoints.2 = GridFace.out) :
    (graph transition).Adj (.inl o) outer := by
  simpa [outer, h] using edge_incident_snd transition o

/-- Distinct occurrence vertices stay distinct even when their geometric edge
labels are equal. -/
theorem edgeVertex_injective :
    Function.Injective (fun o : O =>
      (.inl o : OccurrenceCotreeDualCore (m := m) (n := n) O)) :=
  Sum.inl_injective

private theorem exists_adj_dist_lt_of_reachable_of_ne
    {V : Type*} {G : SimpleGraph V} {x target : V}
    (hreach : G.Reachable x target) (hne : x ≠ target) :
    ∃ y, G.Adj x y ∧ G.dist target y < G.dist target x := by
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hne rfl).elim
  | @cons x y target hxy p =>
      refine ⟨y, hxy, ?_⟩
      have hle : G.dist y target ≤ p.length := dist_le p
      rw [SimpleGraph.dist_comm (G := G) (u := target) (v := y),
        SimpleGraph.dist_comm (G := G) (u := target) (v := x)]
      simp only [Walk.length_cons] at hp
      omega

/-- A chosen shortest-path predecessor toward the outer face.  A component not
reaching `out` is deliberately not assigned a fictitious escape. -/
noncomputable def parent
    (transition : O → LabelledCotreeTransition T)
    (x : OccurrenceCotreeDualCore (m := m) (n := n) O) :
    Option (OccurrenceCotreeDualCore (m := m) (n := n) O) :=
  by
    classical
    exact if hreach : (graph transition).Reachable x outer then
      if houter : x = outer then none
      else some (Classical.choose
        (exists_adj_dist_lt_of_reachable_of_ne hreach houter))
    else none

theorem parent_eq_none_iff
    (x : OccurrenceCotreeDualCore (m := m) (n := n) O) :
    parent transition x = none ↔
      x = outer ∨ ¬(graph transition).Reachable x outer := by
  classical
  by_cases hreach : (graph transition).Reachable x outer
  · simp [parent, hreach]
  · simp [parent, hreach]

@[simp] theorem parent_outer_eq_none :
    parent transition (outer : OccurrenceCotreeDualCore (m := m) (n := n) O) = none :=
  (parent_eq_none_iff transition outer).2 (Or.inl rfl)

theorem parent_adj {x y : OccurrenceCotreeDualCore (m := m) (n := n) O}
    (hparent : parent transition x = some y) :
    (graph transition).Adj x y := by
  classical
  unfold parent at hparent
  split at hparent
  · split at hparent
    · simp at hparent
    · rename_i hreach houter
      have hxy : Classical.choose
          (exists_adj_dist_lt_of_reachable_of_ne hreach houter) = y :=
        Option.some.inj hparent
      rw [← hxy]
      exact (Classical.choose_spec
        (exists_adj_dist_lt_of_reachable_of_ne hreach houter)).1
  · simp at hparent

theorem dist_parent_lt {x y : OccurrenceCotreeDualCore (m := m) (n := n) O}
    (hparent : parent transition x = some y) :
    (graph transition).dist outer y < (graph transition).dist outer x := by
  classical
  unfold parent at hparent
  split at hparent
  · split at hparent
    · simp at hparent
    · rename_i hreach houter
      have hxy : Classical.choose
          (exists_adj_dist_lt_of_reachable_of_ne hreach houter) = y :=
        Option.some.inj hparent
      rw [← hxy]
      exact (Classical.choose_spec
        (exists_adj_dist_lt_of_reachable_of_ne hreach houter)).2
  · simp at hparent

/-- Shortest-dual-distance orientation of the occurrence incidence graph. -/
noncomputable def forest [Fintype O] [DecidableEq O]
    (transition : O → LabelledCotreeTransition T) :
    ParentForest (OccurrenceCotreeDualCore (m := m) (n := n) O) where
  parent := parent transition
  rank x := (graph transition).dist outer x
  rank_parent := dist_parent_lt transition

/-- The incidence construction has the single unsplit outer face as a root.
Split-port freshness is separate geometric data and cannot be read from this
root fact. -/
theorem outer_mem_forest_roots [Fintype O] [DecidableEq O] :
    (outer : OccurrenceCotreeDualCore (m := m) (n := n) O) ∈
      (forest transition).roots := by
  classical
  simp [ParentForest.roots, forest]

end OccurrenceCotreeDualCore

/-- The final carrier distinguishes start labels from the generally larger
universe of edge occurrences used by dual paths. -/
def OccurrenceLabelledCotreeDualCarrier (Start EdgeOccurrence : Type*) :=
  Start ⊕ OccurrenceCotreeDualCore (m := m) (n := n) EdgeOccurrence

/-- Concrete finite edge-occurrence universe retaining debt provenance across
every labelled cotree transition. -/
abbrev ProvenanceCotreeDualOccurrence (Debt : Type*) :=
  Debt × LabelledCotreeTransition T

/-- Edge-occurrence universe for a dual path.  Gap occurrences and continuation
occurrences are a disjoint sum, even when they carry the same coordinate edge.
The two summands therefore retain their different provenance. -/
def CotreeDualEdgeOccurrenceUniverse (GapOccurrence ContinuationOccurrence : Type*) :=
  GapOccurrence ⊕ ContinuationOccurrence

namespace CotreeDualEdgeOccurrenceUniverse

variable {GapOccurrence ContinuationOccurrence : Type*}

/-- Forget only the occurrence kind, never the occurrence itself. -/
def transition
    (gapTransition : GapOccurrence → LabelledCotreeTransition T)
    (continuationTransition : ContinuationOccurrence → LabelledCotreeTransition T) :
    CotreeDualEdgeOccurrenceUniverse GapOccurrence ContinuationOccurrence →
      LabelledCotreeTransition T
  | .inl gap => gapTransition gap
  | .inr continuation => continuationTransition continuation

/-- All selected gap starts embed in the larger edge-occurrence universe. -/
def gapEmbedding : GapOccurrence ↪
    CotreeDualEdgeOccurrenceUniverse GapOccurrence ContinuationOccurrence where
  toFun := Sum.inl
  inj' := Sum.inl_injective

/-- A previously selected family of gap starts embeds without identifying it
with continuation occurrences. -/
def selectedGapEmbedding {Start : Type*} (selected : Start ↪ GapOccurrence) :
    Start ↪ CotreeDualEdgeOccurrenceUniverse GapOccurrence ContinuationOccurrence :=
  selected.trans gapEmbedding

end CotreeDualEdgeOccurrenceUniverse

namespace OccurrenceLabelledCotreeDualCarrier

variable {Start EdgeOccurrence : Type*}
  [Fintype Start] [DecidableEq Start]
  [Fintype EdgeOccurrence] [DecidableEq EdgeOccurrence]
  (transition : EdgeOccurrence → LabelledCotreeTransition T)
  (startEdge : Start → EdgeOccurrence)

noncomputable instance carrierFintype :
    Fintype (OccurrenceLabelledCotreeDualCarrier
      (m := m) (n := n) Start EdgeOccurrence) := by
  unfold OccurrenceLabelledCotreeDualCarrier OccurrenceCotreeDualCore
  infer_instance

noncomputable instance carrierDecidableEq :
    DecidableEq (OccurrenceLabelledCotreeDualCarrier
      (m := m) (n := n) Start EdgeOccurrence) := by
  unfold OccurrenceLabelledCotreeDualCarrier OccurrenceCotreeDualCore
  infer_instance

/-- Extend the distance forest by attaching each occurrence as a private leaf
to its own labelled edge vertex. -/
noncomputable def forest
    (transition : EdgeOccurrence → LabelledCotreeTransition T)
    (startEdge : Start → EdgeOccurrence) :
    ParentForest (OccurrenceLabelledCotreeDualCarrier
      (m := m) (n := n) Start EdgeOccurrence) where
  parent
    | .inl start => some (.inr (.inl (startEdge start)))
    | .inr x => (OccurrenceCotreeDualCore.parent transition x).map Sum.inr
  rank
    | .inl start =>
        (OccurrenceCotreeDualCore.graph transition).dist
          OccurrenceCotreeDualCore.outer (.inl (startEdge start)) + 1
    | .inr x =>
        (OccurrenceCotreeDualCore.graph transition).dist
          OccurrenceCotreeDualCore.outer x
  rank_parent := by
    intro v w hparent
    cases v with
    | inl o =>
        simp only [Option.some.injEq] at hparent
        subst w
        simp
    | inr x =>
        cases hcore : OccurrenceCotreeDualCore.parent transition x with
        | none => simp [hcore] at hparent
        | some y =>
            simp [hcore] at hparent
            subst w
            exact OccurrenceCotreeDualCore.dist_parent_lt transition hcore

theorem no_parent_is_privateLeaf
    (x : OccurrenceLabelledCotreeDualCarrier
      (m := m) (n := n) Start EdgeOccurrence) (start : Start) :
    (forest transition startEdge).parent x ≠ some (.inl start) := by
  cases x <;> simp [forest]

/-- Every occurrence is a leaf, independently of outer connectivity. -/
theorem privateLeaf_mem_leaves (start : Start) :
    (.inl start : OccurrenceLabelledCotreeDualCarrier
      (m := m) (n := n) Start EdgeOccurrence) ∈
      (forest transition startEdge).leaves := by
  classical
  simp only [ParentForest.leaves, Finset.mem_filter, Finset.mem_univ, true_and,
    ParentForest.childCount]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hparent : (forest transition startEdge).parent x = some (.inl start) :=
    (Finset.mem_filter.mp hx).2
  exact no_parent_is_privateLeaf transition startEdge x start hparent

/-- Canonical start-leaf embedding.  This is the intended entry point for the
`FullPrunedInwardCollision` carrier. -/
noncomputable def startLeafEmbedding :
    Start ↪ ↥((forest transition startEdge).leaves) where
  toFun start := ⟨.inl start, privateLeaf_mem_leaves transition startEdge start⟩
  inj' := by
    intro a b hab
    exact Sum.inl.inj (congrArg (fun x => x.1) hab)

end OccurrenceLabelledCotreeDualCarrier

/-! ## Occurrence-split outer incidence -/

/-- Occurrences whose coordinate edge is incident with the unbounded face.
This is an incidence occurrence, not a `GridCotreeOuterPort`: the latter is a
supported primal vertex together with a missing geometric side. -/
def BoundaryTransitionOccurrence {O : Type*}
    (transition : O → LabelledCotreeTransition T) :=
  {o : O //
    (transition o).1.dualEndpoints.1 = GridFace.out ∨
      (transition o).1.dualEndpoints.2 = GridFace.out}

namespace BoundaryTransitionOccurrence

variable {O : Type*} (transition : O → LabelledCotreeTransition T)

/-- We consistently use the first endpoint of the oriented coordinate edge.
Membership of the edge in the cotree proves that this endpoint is supported. -/
def supportedEndpoint (o : BoundaryTransitionOccurrence transition) :
    GridVertex m n :=
  (transition o.1).1.primalEndpoints.1

theorem supportedEndpoint_mem (o : BoundaryTransitionOccurrence transition) :
    supportedEndpoint transition o ∈ supportFinset (gridGraph m n \ T) := by
  rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
  refine ⟨(transition o.1).1.primalEndpoints.2, ?_⟩
  have h := (transition o.1).2
  rw [SimpleGraph.mem_edgeFinset] at h
  simpa [supportedEndpoint, GridEdge.primalSym2] using h

/-- The geometric side through which the coordinate edge meets `out`.  The
`2 ≤ m,n` hypotheses exclude a coordinate edge having `out` on both sides. -/
def side (hm : 2 ≤ m) (hn : 2 ≤ n)
    (o : BoundaryTransitionOccurrence transition) : OuterBoundarySide :=
  match (transition o.1).1 with
  | .horizontal e => if e.row.val = 0 then .top else .bottom
  | .vertical e => if e.col.val = 0 then .left else .right

theorem side_incidence (hm : 2 ≤ m) (hn : 2 ≤ n)
    (o : BoundaryTransitionOccurrence transition) :
    match side transition hm hn o with
    | .top => (supportedEndpoint transition o).1.val = 0
    | .bottom => (supportedEndpoint transition o).1.val + 1 = m
    | .left => (supportedEndpoint transition o).2.val = 0
    | .right => (supportedEndpoint transition o).2.val + 1 = n := by
  rcases o with ⟨o, hout⟩
  cases hlabel : (transition o).1 with
  | horizontal e =>
      change _ at hout ⊢
      by_cases htop : e.row.val = 0
      · simpa [side, supportedEndpoint, hlabel, htop, GridEdge.primalEndpoints,
          horizontalPrimalEndpoints] using htop
      · have hbottom : e.row.val + 1 = m := by
          simp [hlabel, GridEdge.dualEndpoints, horizontalDualEndpoints, htop] at hout
          exact hout
        simpa [side, supportedEndpoint, hlabel, htop, GridEdge.primalEndpoints,
          horizontalPrimalEndpoints] using hbottom
  | vertical e =>
      change _ at hout ⊢
      by_cases hleft : e.col.val = 0
      · simpa [side, supportedEndpoint, hlabel, hleft, GridEdge.primalEndpoints,
          verticalPrimalEndpoints] using hleft
      · have hright : e.col.val + 1 = n := by
          simp [hlabel, GridEdge.dualEndpoints, verticalDualEndpoints, hleft] at hout
          exact hout
        simpa [side, supportedEndpoint, hlabel, hleft, GridEdge.primalEndpoints,
          verticalPrimalEndpoints] using hright

/-- A boundary-edge occurrence has a canonical supported endpoint-side port.
This map does not assert that different occurrences use different ports. -/
def outerPort (hm : 2 ≤ m) (hn : 2 ≤ n)
    (o : BoundaryTransitionOccurrence transition) : GridCotreeOuterPort T :=
  OuterBoundaryPort.ofSupportedVertexSide
    (supportedEndpoint transition o) (supportedEndpoint_mem transition o)
    (side transition hm hn o) (side_incidence transition hm hn o)

@[simp] theorem outerPort_vertex (hm : 2 ≤ m) (hn : 2 ≤ n)
    (o : BoundaryTransitionOccurrence transition) :
    (outerPort transition hm hn o).vertex = supportedEndpoint transition o :=
  OuterBoundaryPort.vertex_ofSupportedVertexSide _ _ _ _

@[simp] theorem outerPort_side (hm : 2 ≤ m) (hn : 2 ≤ n)
    (o : BoundaryTransitionOccurrence transition) :
    (outerPort transition hm hn o).side = side transition hm hn o :=
  OuterBoundaryPort.side_ofSupportedVertexSide _ _ _ _

/-- A boundary coordinate edge is determined by the endpoint-side port chosen
by its canonical orientation. -/
theorem edge_eq_of_outerPort_eq (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a b : BoundaryTransitionOccurrence transition}
    (hport : outerPort transition hm hn a = outerPort transition hm hn b) :
    (transition a.1).1 = (transition b.1).1 := by
  have hv : supportedEndpoint transition a = supportedEndpoint transition b := by
    simpa using congrArg OuterBoundaryPort.vertex hport
  have hs : side transition hm hn a = side transition hm hn b := by
    simpa using congrArg OuterBoundaryPort.side hport
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases hea : (transition a).1 with
  | horizontal ea =>
      cases heb : (transition b).1 with
      | horizontal eb =>
          congr 1
          apply horizontalGridEdge_eq_of_row_eq_of_col_val_eq
          · simpa [supportedEndpoint, hea, heb, GridEdge.primalEndpoints,
              horizontalPrimalEndpoints] using congrArg Prod.fst hv
          · simpa [supportedEndpoint, hea, heb, GridEdge.primalEndpoints,
              horizontalPrimalEndpoints] using congrArg (fun v => v.2.val) hv
      | vertical eb =>
          simp [side, hea, heb] at hs
          split at hs <;> split at hs <;> contradiction
  | vertical ea =>
      cases heb : (transition b).1 with
      | horizontal eb =>
          simp [side, hea, heb] at hs
          split at hs <;> split at hs <;> contradiction
      | vertical eb =>
          congr 1
          apply verticalGridEdge_eq_of_row_eq_of_col_val_eq
          · apply Fin.ext
            simpa [supportedEndpoint, hea, heb, GridEdge.primalEndpoints,
              verticalPrimalEndpoints] using congrArg (fun v => v.1.val) hv
          · simpa [supportedEndpoint, hea, heb, GridEdge.primalEndpoints,
              verticalPrimalEndpoints] using congrArg (fun v => v.2.val) hv

/-- The precise extra endpoint-choice condition needed to classify private
outer roots by physical ports: no two boundary occurrences choose the same
supported endpoint and side. -/
def PortChoiceInjective (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  Function.Injective (outerPort transition hm hn)

/-- If boundary occurrences are unique by actual coordinate edge, their
canonical endpoint-side ports are injective. -/
theorem portChoiceInjective_of_edge_injective (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hedge : Function.Injective fun o : BoundaryTransitionOccurrence transition =>
      (transition o.1).1) : PortChoiceInjective transition hm hn := by
  intro a b hab
  exact hedge (edge_eq_of_outerPort_eq transition hm hn hab)

theorem portChoiceInjective_iff (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PortChoiceInjective transition hm hn ↔
      ∀ a b, supportedEndpoint transition a = supportedEndpoint transition b →
        side transition hm hn a = side transition hm hn b → a = b := by
  constructor
  · intro hinj a b hv hs
    apply hinj
    apply OuterBoundaryPort.eq_of_vertex_eq_of_side_eq
    · simpa using hv
    · simpa using hs
  · intro h a b hab
    apply h a b
    · simpa using congrArg OuterBoundaryPort.vertex hab
    · simpa using congrArg OuterBoundaryPort.side hab

end BoundaryTransitionOccurrence

/-- Split incidence carrier: edge occurrences, shared bounded faces, and one
private outer-incidence vertex for every boundary occurrence. -/
def SplitOccurrenceCotreeDualCore {O : Type*}
    (transition : O → LabelledCotreeTransition T) :=
  O ⊕ ({f : GridFace m n // f ≠ GridFace.out} ⊕
    BoundaryTransitionOccurrence transition)

noncomputable instance boundaryTransitionOccurrenceFintype
    {O : Type*} [Fintype O] (transition : O → LabelledCotreeTransition T) :
    Fintype (BoundaryTransitionOccurrence transition) := by
  classical
  unfold BoundaryTransitionOccurrence
  infer_instance

noncomputable instance splitOccurrenceCotreeDualCoreFintype
    {O : Type*} [Fintype O] (transition : O → LabelledCotreeTransition T) :
    Fintype (SplitOccurrenceCotreeDualCore transition) := by
  classical
  unfold SplitOccurrenceCotreeDualCore
  infer_instance

noncomputable instance splitOccurrenceCotreeDualCoreDecidableEq
    {O : Type*} [DecidableEq O] (transition : O → LabelledCotreeTransition T) :
    DecidableEq (SplitOccurrenceCotreeDualCore transition) := by
  classical
  unfold SplitOccurrenceCotreeDualCore
  infer_instance

namespace SplitOccurrenceCotreeDualCore

variable {O : Type*} (transition : O → LabelledCotreeTransition T)

def IsOuter : SplitOccurrenceCotreeDualCore transition → Prop
  | .inr (.inr _) => True
  | _ => False

/-- Incidence after replacing every occurrence of `GridFace.out` by that
occurrence's private split vertex. -/
def Incident (o : O) :
    ({f : GridFace m n // f ≠ GridFace.out} ⊕
      BoundaryTransitionOccurrence transition) → Prop
  | .inl f => f.1 = (transition o).1.dualEndpoints.1 ∨
      f.1 = (transition o).1.dualEndpoints.2
  | .inr b => b.1 = o

def graph : SimpleGraph (SplitOccurrenceCotreeDualCore transition) where
  Adj
    | .inl o, .inr x => Incident transition o x
    | .inr x, .inl o => Incident transition o x
    | _, _ => False
  symm := by intro x y h; cases x <;> cases y <;> simp_all
  loopless := by intro x h; cases x <;> simp_all

noncomputable instance graphDecidableRel [DecidableEq O] :
    DecidableRel (graph transition).Adj := by
  classical
  intro x y
  infer_instance

theorem edge_incident_privateOuter
    (b : BoundaryTransitionOccurrence transition) :
    (graph transition).Adj (.inl b.1) (.inr (.inr b)) := rfl

theorem privateOuter_injective : Function.Injective
    (fun b : BoundaryTransitionOccurrence transition =>
      (.inr (.inr b) : SplitOccurrenceCotreeDualCore transition)) := by
  intro a b h
  exact Sum.inr.inj (Sum.inr.inj h)

theorem bounded_incidence_iff (o : O) (f : GridFace m n)
    (hf : f ≠ GridFace.out) :
    (graph transition).Adj (.inl o) (.inr (.inl ⟨f, hf⟩)) ↔
      f = (transition o).1.dualEndpoints.1 ∨
        f = (transition o).1.dualEndpoints.2 := Iff.rfl

/-- An auxiliary hub joins all private outer incidences.  It is used only as a
common shortest-path target and is not a vertex of the split forest. -/
def RoutingVertex := SplitOccurrenceCotreeDualCore transition ⊕ Unit

def hub : RoutingVertex transition := .inr ()

def routingGraph : SimpleGraph (RoutingVertex transition) where
  Adj
    | .inl x, .inl y => (graph transition).Adj x y
    | .inl x, .inr _ => IsOuter transition x
    | .inr _, .inl x => IsOuter transition x
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all
    exact (graph transition).symm h
  loopless := by intro x h; cases x <;> simp_all

noncomputable instance routingGraphDecidableRel [DecidableEq O] :
    DecidableRel (routingGraph transition).Adj := by
  classical
  intro x y
  infer_instance

private theorem exists_core_parent
    {x : SplitOccurrenceCotreeDualCore transition}
    (hreach : (routingGraph transition).Reachable (.inl x) (hub transition))
    (houter : ¬IsOuter transition x) :
    ∃ y : SplitOccurrenceCotreeDualCore transition,
      (graph transition).Adj x y ∧
        (routingGraph transition).dist (hub transition) (.inl y) <
          (routingGraph transition).dist (hub transition) (.inl x) := by
  obtain ⟨z, hxz, hdist⟩ :=
    OccurrenceCotreeDualCore.exists_adj_dist_lt_of_reachable_of_ne
      hreach (by intro h; cases h)
  cases z with
  | inl y => exact ⟨y, hxz, hdist⟩
  | inr u => exact (houter hxz).elim

noncomputable def parent [DecidableEq O]
    (x : SplitOccurrenceCotreeDualCore transition) :
    Option (SplitOccurrenceCotreeDualCore transition) := by
  classical
  exact if houter : IsOuter transition x then none
    else if hreach : (routingGraph transition).Reachable (.inl x) (hub transition)
      then some (Classical.choose (exists_core_parent transition hreach houter))
      else none

theorem parent_eq_none_iff [DecidableEq O]
    (x : SplitOccurrenceCotreeDualCore transition) :
    parent transition x = none ↔
      IsOuter transition x ∨
        ¬(routingGraph transition).Reachable (.inl x) (hub transition) := by
  classical
  by_cases ho : IsOuter transition x <;>
    by_cases hr : (routingGraph transition).Reachable (.inl x) (hub transition) <;>
    simp [parent, ho, hr]

theorem parent_adj [DecidableEq O]
    {x y : SplitOccurrenceCotreeDualCore transition}
    (h : parent transition x = some y) : (graph transition).Adj x y := by
  classical
  by_cases ho : IsOuter transition x
  · simp [parent, ho] at h
  · by_cases hr : (routingGraph transition).Reachable (.inl x) (hub transition)
    · have hy : Classical.choose (exists_core_parent transition hr ho) = y := by
        simpa [parent, ho, hr] using h
      rw [← hy]
      exact (Classical.choose_spec (exists_core_parent transition hr ho)).1
    · simp [parent, ho, hr] at h

theorem dist_parent_lt [DecidableEq O]
    {x y : SplitOccurrenceCotreeDualCore transition}
    (h : parent transition x = some y) :
    (routingGraph transition).dist (hub transition) (.inl y) <
      (routingGraph transition).dist (hub transition) (.inl x) := by
  classical
  by_cases ho : IsOuter transition x
  · simp [parent, ho] at h
  · by_cases hr : (routingGraph transition).Reachable (.inl x) (hub transition)
    · have hy : Classical.choose (exists_core_parent transition hr ho) = y := by
        simpa [parent, ho, hr] using h
      rw [← hy]
      exact (Classical.choose_spec (exists_core_parent transition hr ho)).2
    · simp [parent, ho, hr] at h

/-- Alternative shortest-path parent tie-breaking.  Geometry may replace the
unconstrained `Classical.choose` parent while retaining the same routing rank. -/
structure ParentTieBreaking where
  parent : SplitOccurrenceCotreeDualCore transition →
    Option (SplitOccurrenceCotreeDualCore transition)
  parent_adj : ∀ {x y}, parent x = some y → (graph transition).Adj x y
  dist_parent_lt : ∀ {x y}, parent x = some y →
    (routingGraph transition).dist (hub transition) (.inl y) <
      (routingGraph transition).dist (hub transition) (.inl x)

/-- All admissible parents of `x`: incident core vertices one step closer to
the routing hub.  Keeping this set explicit lets geometric code order the
choices without hiding another `Classical.choose`. -/
noncomputable def shortestParentCandidates [Fintype O] [DecidableEq O]
    (x : SplitOccurrenceCotreeDualCore transition) :
    Finset (SplitOccurrenceCotreeDualCore transition) := by
  classical
  exact Finset.univ.filter fun y =>
    (graph transition).Adj x y ∧
      (routingGraph transition).dist (hub transition) (.inl y) <
        (routingGraph transition).dist (hub transition) (.inl x)

theorem mem_shortestParentCandidates [Fintype O] [DecidableEq O]
    {x y : SplitOccurrenceCotreeDualCore transition} :
    y ∈ shortestParentCandidates transition x ↔
      (graph transition).Adj x y ∧
        (routingGraph transition).dist (hub transition) (.inl y) <
          (routingGraph transition).dist (hub transition) (.inl x) := by
  simp [shortestParentCandidates]

theorem shortestParentCandidates_nonempty [Fintype O] [DecidableEq O]
    {x : SplitOccurrenceCotreeDualCore transition}
    (hreach : (routingGraph transition).Reachable (.inl x) (hub transition))
    (houter : ¬IsOuter transition x) :
    (shortestParentCandidates transition x).Nonempty := by
  obtain ⟨y, hadj, hdist⟩ := exists_core_parent transition hreach houter
  exact ⟨y, (mem_shortestParentCandidates transition).2 ⟨hadj, hdist⟩⟩

/-- Deterministic shortest-parent selection for a caller-supplied geometric
order.  In grid applications the order can be the lexicographic
coordinate/rotation order on occurrences and faces. -/
noncomputable def orderedTieBreaking [Fintype O] [DecidableEq O]
    (order : LinearOrder (SplitOccurrenceCotreeDualCore transition)) :
    ParentTieBreaking transition := by
  classical
  letI := order
  let orderedParent : SplitOccurrenceCotreeDualCore transition →
      Option (SplitOccurrenceCotreeDualCore transition) := fun x =>
    if houter : IsOuter transition x then none
    else if hreach : (routingGraph transition).Reachable (.inl x) (hub transition) then
      some ((shortestParentCandidates transition x).min'
        (shortestParentCandidates_nonempty transition hreach houter))
    else none
  refine
    { parent := orderedParent
      parent_adj := ?_
      dist_parent_lt := ?_ }
  · intro x y hparent
    dsimp only [orderedParent] at hparent
    split at hparent
    · simp at hparent
    · split at hparent
      · rename_i houter hreach
        have hy : (shortestParentCandidates transition x).min'
            (shortestParentCandidates_nonempty transition hreach houter) = y :=
          Option.some.inj hparent
        rw [← hy]
        exact ((mem_shortestParentCandidates transition).1
          (Finset.min'_mem _ _)).1
      · simp at hparent
  · intro x y hparent
    dsimp only [orderedParent] at hparent
    split at hparent
    · simp at hparent
    · split at hparent
      · rename_i houter hreach
        have hy : (shortestParentCandidates transition x).min'
            (shortestParentCandidates_nonempty transition hreach houter) = y :=
          Option.some.inj hparent
        rw [← hy]
        exact ((mem_shortestParentCandidates transition).1
          (Finset.min'_mem _ _)).2
      · simp at hparent

/-- The minimal forest redesign: only the choice among distance-decreasing
incident parents changes.  A sector/resource construction should instantiate
this with a collision-separating choice rather than relying on arbitrary
shortest-path choice. -/
noncomputable def ParentTieBreaking.forest [Fintype O] [DecidableEq O]
    (choice : ParentTieBreaking transition) :
    ParentForest (SplitOccurrenceCotreeDualCore transition) where
  parent := choice.parent
  rank x := (routingGraph transition).dist (hub transition) (.inl x)
  rank_parent := choice.dist_parent_lt

/-- The current canonical arbitrary shortest-path choice as explicit
tie-breaking data. -/
noncomputable def shortestPathTieBreaking [DecidableEq O] :
    ParentTieBreaking transition where
  parent := parent transition
  parent_adj := parent_adj transition
  dist_parent_lt := dist_parent_lt transition

/-- Reachability forest oriented toward the occurrence-split outer boundary. -/
noncomputable def forest [Fintype O] [DecidableEq O] :
    ParentForest (SplitOccurrenceCotreeDualCore transition) where
  parent := parent transition
  rank x := (routingGraph transition).dist (hub transition) (.inl x)
  rank_parent := dist_parent_lt transition

theorem mem_roots_iff [Fintype O] [DecidableEq O]
    (x : SplitOccurrenceCotreeDualCore transition) :
    x ∈ (forest transition).roots ↔
      IsOuter transition x ∨
        ¬(routingGraph transition).Reachable (.inl x) (hub transition) := by
  simp [ParentForest.roots, forest, parent_eq_none_iff]

/-- Exact connectivity hypothesis needed to rule out bounded roots.  It is
deliberately a property of the supplied occurrence universe: omitted geometric
edges absent from that universe cannot be traversed by `routingGraph`. -/
def ReachesSplitOuterBoundary : Prop :=
  ∀ x : SplitOccurrenceCotreeDualCore transition,
    (routingGraph transition).Reachable (.inl x) (hub transition)

/-- Under exact occurrence-level boundary connectivity, the only roots are the
private split outer incidences. -/
theorem mem_roots_iff_isOuter [Fintype O] [DecidableEq O]
    (hconnected : ReachesSplitOuterBoundary transition)
    (x : SplitOccurrenceCotreeDualCore transition) :
    x ∈ (forest transition).roots ↔ IsOuter transition x := by
  rw [mem_roots_iff]
  simp [hconnected x]

/-! ## Full-cotree universes and continuation lifting -/

/-- The exact finite-grid tree-cotree statement, expressed in the occurrence
incidence graph with one occurrence for every actual cotree edge.  Splitting
the outer face is harmless here: its private occurrences are joined only by
the auxiliary routing hub. -/
def GridSpanningTreeCotreeDualBoundaryConnectivity
    (hT : IsSpanningSubtree (gridGraph m n) T) : Prop :=
  ReachesSplitOuterBoundary (fun e : LabelledCotreeTransition T => e)

/-- The face immediately counterclockwise from a compass slot. -/
private def faceBeforeSlot (s : GridCompassSlot m n) : GridFace m n :=
  match s.2 with
  | .north => if hr : s.1.1.val = 0 then .out else
      if hc : s.1.2.val = 0 then .out else
        .cell ⟨s.1.1.val - 1, by omega⟩ ⟨s.1.2.val - 1, by omega⟩
  | .east => if hr : s.1.1.val = 0 then .out else
      if hc : s.1.2.val + 1 = n then .out else
        .cell ⟨s.1.1.val - 1, by omega⟩ ⟨s.1.2.val, by omega⟩
  | .south => if hr : s.1.1.val + 1 = m then .out else
      if hc : s.1.2.val + 1 = n then .out else
        .cell ⟨s.1.1.val, by omega⟩ ⟨s.1.2.val, by omega⟩
  | .west => if hr : s.1.1.val + 1 = m then .out else
      if hc : s.1.2.val = 0 then .out else
        .cell ⟨s.1.1.val, by omega⟩ ⟨s.1.2.val - 1, by omega⟩

private theorem faceBeforeSlot_succ_of_occupied
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (s : GridCompassSlot m n) (h : GridExpandedContour.Occupied (T := T) s) :
    faceBeforeSlot (GridExpandedContour.succ (T := T) s) = faceBeforeSlot s := by
  rcases s with ⟨v, d⟩
  rw [GridExpandedContour.succ_of_occupied h]
  let dart := GridDirectionalDart.ofDirectionMem (T := T) v d h
  have hstep := dart.step
  fin_cases d
  · by_cases hv : 0 < v.1.val
    · change gridNeighbor? v .north = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep
      rw [← hstep]
      simp only [faceBeforeSlot, GridDirection.opposite, GridDirection.clockwise,
        Prod.fst, Prod.snd, Fin.isValue] <;>
        split_ifs <;> try omega
      all_goals try rfl
      all_goals congr 1 <;> apply Fin.ext <;> omega
    · change gridNeighbor? v .north = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep
  · have hv : v.2.val + 1 < n := by
      by_contra hv
      change gridNeighbor? v .east = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep
    change gridNeighbor? v .east = some dart.target at hstep
    simp [gridNeighbor?, hv] at hstep
    rw [← hstep]
    simp only [faceBeforeSlot, GridDirection.opposite, GridDirection.clockwise,
      Prod.fst, Prod.snd, Fin.isValue] <;>
      split_ifs <;> try omega
    all_goals try rfl
    all_goals congr 1 <;> apply Fin.ext <;> omega
  · have hv : v.1.val + 1 < m := by
      by_contra hv
      change gridNeighbor? v .south = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep
    change gridNeighbor? v .south = some dart.target at hstep
    simp [gridNeighbor?, hv] at hstep
    rw [← hstep]
    simp only [faceBeforeSlot, GridDirection.opposite, GridDirection.clockwise,
      Prod.fst, Prod.snd, Fin.isValue] <;>
      split_ifs <;> try omega
    all_goals try rfl
    all_goals congr 1 <;> apply Fin.ext <;> omega
  · by_cases hv : 0 < v.2.val
    · change gridNeighbor? v .west = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep
      rw [← hstep]
      simp only [faceBeforeSlot, GridDirection.opposite, GridDirection.clockwise,
        Prod.fst, Prod.snd, Fin.isValue] <;>
        split_ifs <;> try omega
      all_goals try rfl
      all_goals congr 1 <;> apply Fin.ext <;> omega
    · change gridNeighbor? v .west = some dart.target at hstep
      simp [gridNeighbor?, hv] at hstep

/-- Finite cell-boundary cancellation, stated for coordinate-labelled edges. -/
theorem exists_faceCut_crossing_not_adj_of_isAcyclic
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hTle : T ≤ gridGraph m n) (htree : T.IsTree)
    (S : Set (GridFace m n)) (hne : S.Nonempty)
    (hout : GridFace.out ∉ S) :
    ∃ e : GridEdge m n,
      ((e.dualEndpoints.1 ∈ S ∧ e.dualEndpoints.2 ∉ S) ∨
        (e.dualEndpoints.2 ∈ S ∧ e.dualEndpoints.1 ∉ S)) ∧
      ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsame (s : GridCompassSlot m n) :
      faceBeforeSlot (GridExpandedContour.succ (T := T) s) ∈ S ↔
        faceBeforeSlot s ∈ S := by
    by_cases hoccupied : GridExpandedContour.Occupied (T := T) s
    · rw [faceBeforeSlot_succ_of_occupied s hoccupied]
    rcases s with ⟨v, d⟩
    rw [GridExpandedContour.succ_of_not_occupied hoccupied]
    fin_cases d
    · by_cases hr : v.1.val = 0
      · have hn1 : n ≠ 1 := by omega
        simp [faceBeforeSlot, GridDirection.clockwise, hr, hn1]
      · let e : GridEdge m n := .vertical
          ⟨⟨v.1.val - 1, by
            have hvlt := v.1.isLt
            omega⟩, v.2⟩
        have hnotT : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
          intro hadj
          apply hoccupied
          change GridDirection.north ∈ GridDirectionalDart.directionsAt (T := T) v
          rw [GridDirectionalDart.mem_directionsAt]
          refine ⟨e.primalEndpoints.1, ?_, ?_⟩
          · simp [e, GridEdge.primalEndpoints, verticalPrimalEndpoints,
              gridNeighbor?, Fin.ext_iff] <;> omega
          · convert hadj.symm using 1 <;>
              apply Prod.ext <;> apply Fin.ext <;>
              simp [e, GridEdge.primalEndpoints, verticalPrimalEndpoints] <;> omega
        have hnocross := mt (hnone e) hnotT
        simp [e, GridEdge.dualEndpoints, verticalDualEndpoints, faceBeforeSlot,
          hr, Fin.ext_iff] at hnocross ⊢
        tauto
    · by_cases hc : v.2.val + 1 = n
      · have hm1 : m ≠ 1 := by omega
        simp [faceBeforeSlot, GridDirection.clockwise, hc, hm1]
      · have hvn := v.2.isLt
        have hvlt : v.2.val < n - 1 := by omega
        let e : GridEdge m n := .horizontal ⟨v.1, ⟨v.2.val, hvlt⟩⟩
        have hnotT : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
          intro hadj
          apply hoccupied
          change GridDirection.east ∈ GridDirectionalDart.directionsAt (T := T) v
          rw [GridDirectionalDart.mem_directionsAt]
          refine ⟨e.primalEndpoints.2, ?_, hadj⟩
          have : v.2.val + 1 < n := by omega
          simp [e, GridEdge.primalEndpoints, horizontalPrimalEndpoints,
            gridNeighbor?, Fin.ext_iff, this]
        have hnocross := mt (hnone e) hnotT
        simp [e, GridEdge.dualEndpoints, horizontalDualEndpoints, faceBeforeSlot,
          hc, Fin.ext_iff] at hnocross ⊢
        tauto
    · by_cases hr : v.1.val + 1 = m
      · have hn1 : n ≠ 1 := by omega
        simp [faceBeforeSlot, GridDirection.clockwise, hr, hn1]
      · have hvm := v.1.isLt
        have hvlt : v.1.val < m - 1 := by omega
        let e : GridEdge m n := .vertical ⟨⟨v.1.val, hvlt⟩, v.2⟩
        have hnotT : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
          intro hadj
          apply hoccupied
          change GridDirection.south ∈ GridDirectionalDart.directionsAt (T := T) v
          rw [GridDirectionalDart.mem_directionsAt]
          refine ⟨e.primalEndpoints.2, ?_, hadj⟩
          have : v.1.val + 1 < m := by omega
          simp [e, GridEdge.primalEndpoints, verticalPrimalEndpoints,
            gridNeighbor?, Fin.ext_iff, this]
        have hnocross := mt (hnone e) hnotT
        simp [e, GridEdge.dualEndpoints, verticalDualEndpoints, faceBeforeSlot,
          hr, Fin.ext_iff] at hnocross ⊢
        tauto
    · by_cases hc : v.2.val = 0
      · have hm1 : m ≠ 1 := by omega
        simp [faceBeforeSlot, GridDirection.clockwise, hc, hm1]
      · let e : GridEdge m n := .horizontal
          ⟨v.1, ⟨v.2.val - 1, by
            have hvlt := v.2.isLt
            omega⟩⟩
        have hnotT : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
          intro hadj
          apply hoccupied
          change GridDirection.west ∈ GridDirectionalDart.directionsAt (T := T) v
          rw [GridDirectionalDart.mem_directionsAt]
          refine ⟨e.primalEndpoints.1, ?_, ?_⟩
          · simp [e, GridEdge.primalEndpoints, horizontalPrimalEndpoints,
              gridNeighbor?, Fin.ext_iff] <;> omega
          · convert hadj.symm using 1 <;>
              apply Prod.ext <;> apply Fin.ext <;>
              simp [e, GridEdge.primalEndpoints, horizontalPrimalEndpoints] <;> omega
        have hnocross := mt (hnone e) hnotT
        simp [e, GridEdge.dualEndpoints, horizontalDualEndpoints, faceBeforeSlot,
          hc, Fin.ext_iff] at hnocross ⊢
        tauto
  obtain ⟨f, hfS⟩ := hne
  cases f with
  | out => exact hout hfS
  | cell r c =>
      let inside : GridCompassSlot m n :=
        ((⟨r.val + 1, by omega⟩, ⟨c.val + 1, by omega⟩), .north)
      let outside : GridCompassSlot m n :=
        ((⟨0, by omega⟩, ⟨0, by omega⟩), .north)
      have hins : faceBeforeSlot inside ∈ S := by
        simpa [inside, faceBeforeSlot, Fin.ext_iff] using hfS
      have houtside : faceBeforeSlot outside ∉ S := by
        simpa [outside, faceBeforeSlot] using hout
      have hcycle := GridExpandedContour.equiv_sameCycle_of_spanningTree
        (T := T) (by nlinarith) ⟨hTle, htree⟩ inside outside
      obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
      have hiter : ∀ k : Nat,
          faceBeforeSlot ((GridExpandedContour.equiv (T := T) ^ k) inside) ∈ S ↔
            faceBeforeSlot inside ∈ S := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            rw [pow_succ', Equiv.Perm.mul_apply]
            exact (hsame _).trans ih
      exact houtside (by simpa [hk] using (hiter k).2 hins)

/-- The dual complement of a rectangular-grid spanning tree reaches the split
outer boundary.  If not, the bounded faces in one unreachable routing
component form a nonempty face cut.  Every primal edge crossing that cut must
belong to the tree, contradicting finite grid cell-boundary cancellation and
acyclicity. -/
theorem gridSpanningTreeCotreeDualBoundaryConnectivity
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    GridSpanningTreeCotreeDualBoundaryConnectivity (T := T) hT := by
  classical
  let transition := fun e : LabelledCotreeTransition T => e
  intro x
  by_contra hfail
  have failed_of_reachable {y : SplitOccurrenceCotreeDualCore transition}
      (hyx : (routingGraph transition).Reachable (.inl y) (.inl x)) :
      ¬(routingGraph transition).Reachable (.inl y) (hub transition) := by
    intro hy
    exact hfail (hyx.symm.trans hy)
  have hnotOuter : ¬IsOuter transition x := by
    intro hx
    exact hfail (SimpleGraph.Adj.reachable (by
      simpa [routingGraph, hub] using hx))
  obtain ⟨f, hfx⟩ : ∃ f : {f : GridFace m n // f ≠ GridFace.out},
      (routingGraph transition).Reachable
        (.inl (.inr (.inl f))) (.inl x) := by
    cases x with
    | inl e =>
        have hone : e.1.dualEndpoints.1 ≠ GridFace.out ∨
            e.1.dualEndpoints.2 ≠ GridFace.out := by
          by_contra h
          push_neg at h
          cases he : e.1 with
          | horizontal a =>
              simp [he, GridEdge.dualEndpoints, horizontalDualEndpoints] at h
              omega
          | vertical a =>
              simp [he, GridEdge.dualEndpoints, verticalDualEndpoints] at h
              omega
        rcases hone with hbounded | hbounded
        · refine ⟨⟨e.1.dualEndpoints.1, hbounded⟩, ?_⟩
          exact SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
            (.inl (.inr (.inl ⟨e.1.dualEndpoints.1, hbounded⟩)))
              (.inl (.inl e)) by exact Or.inl rfl)
        · refine ⟨⟨e.1.dualEndpoints.2, hbounded⟩, ?_⟩
          exact SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
            (.inl (.inr (.inl ⟨e.1.dualEndpoints.2, hbounded⟩)))
              (.inl (.inl e)) by exact Or.inr rfl)
    | inr y =>
        cases y with
        | inl f => exact ⟨f, SimpleGraph.Reachable.refl _⟩
        | inr b => exact (hnotOuter trivial).elim
  let hfout := f.2
  let S : Set (GridFace m n) := fun g =>
    ∃ hg : g ≠ GridFace.out,
      (routingGraph transition).Reachable
        (.inl (.inr (.inl ⟨g, hg⟩)))
        (.inl (.inr (.inl f)))
  have hSne : S.Nonempty := ⟨f.1, f.2, SimpleGraph.Reachable.refl _⟩
  have hout : GridFace.out ∉ S := by
    rintro ⟨h, _⟩
    exact h rfl
  obtain ⟨e, hcross, hnotT⟩ :=
    exists_faceCut_crossing_not_adj_of_isAcyclic hm hn
      hT.1 hT.2 S hSne hout
  apply hnotT
  have heGrid : (gridGraph m n).Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
    cases e <;> simp [GridEdge.primalEndpoints,
      horizontalPrimalEndpoints_adj, verticalPrimalEndpoints_adj]
  by_contra heT
  have heDiff : e.primalSym2 ∈ (gridGraph m n \ T).edgeFinset := by
    simp only [SimpleGraph.edgeFinset_sdiff, Finset.mem_sdiff,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨GridEdge.primalSym2_mem_gridGraph_edgeSet e, by
      simpa [GridEdge.primalSym2] using heT⟩
  let o : LabelledCotreeTransition T := ⟨e, heDiff⟩
  rcases hcross with ⟨hfst, hsnd⟩ | ⟨hsnd, hfst⟩
  · obtain ⟨hfstout, hfstReach⟩ := hfst
    have hsndout : e.dualEndpoints.2 ≠ GridFace.out := by
      intro h
      let b : BoundaryTransitionOccurrence transition :=
        ⟨o, Or.inr h⟩
      apply failed_of_reachable hfx
      exact hfstReach.symm.trans
        ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
          (.inl (.inr (.inl ⟨e.dualEndpoints.1, hfstout⟩))) (.inl (.inl o)) by
            exact Or.inl rfl)).trans
          ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
            (.inl (.inl o)) (.inl (.inr (.inr b))) by rfl)).trans
            (SimpleGraph.Adj.reachable (by
              simp [routingGraph, hub, IsOuter]))))
    have hsndReach : (routingGraph transition).Reachable
        (.inl (.inr (.inl ⟨e.dualEndpoints.2, hsndout⟩)))
        (.inl (.inr (.inl f))) := by
      exact (SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
        (.inl (.inr (.inl ⟨e.dualEndpoints.2, hsndout⟩))) (.inl (.inl o)) by
          exact Or.inr rfl)).trans
        ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
          (.inl (.inl o)) (.inl (.inr (.inl ⟨e.dualEndpoints.1, hfstout⟩))) by
            exact Or.inl rfl)).trans hfstReach)
    exact hsnd ⟨hsndout, hsndReach⟩
  · obtain ⟨hsndout, hsndReach⟩ := hsnd
    have hfstout : e.dualEndpoints.1 ≠ GridFace.out := by
      intro h
      let b : BoundaryTransitionOccurrence transition :=
        ⟨o, Or.inl h⟩
      apply failed_of_reachable hfx
      exact hsndReach.symm.trans
        ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
          (.inl (.inr (.inl ⟨e.dualEndpoints.2, hsndout⟩))) (.inl (.inl o)) by
            exact Or.inr rfl)).trans
          ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
            (.inl (.inl o)) (.inl (.inr (.inr b))) by rfl)).trans
            (SimpleGraph.Adj.reachable (by
              simp [routingGraph, hub, IsOuter]))))
    have hfstReach : (routingGraph transition).Reachable
        (.inl (.inr (.inl ⟨e.dualEndpoints.1, hfstout⟩)))
        (.inl (.inr (.inl f))) := by
      exact (SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
        (.inl (.inr (.inl ⟨e.dualEndpoints.1, hfstout⟩))) (.inl (.inl o)) by
          exact Or.inl rfl)).trans
        ((SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
          (.inl (.inl o)) (.inl (.inr (.inl ⟨e.dualEndpoints.2, hsndout⟩))) by
            exact Or.inr rfl)).trans hsndReach)
    exact hfst ⟨hfstout, hfstReach⟩

/-- Square-grid specialization used by the contour construction. -/
theorem gridSpanningTreeCotreeDualBoundaryConnectivity_square
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    GridSpanningTreeCotreeDualBoundaryConnectivity (T := T) hT :=
  gridSpanningTreeCotreeDualBoundaryConnectivity (by omega) (by omega) hT

/-- An occurrence universe containing a continuation copy of every actual
cotree edge inherits split-boundary connectivity from the full universe. -/
theorem reachesSplitOuterBoundary_of_fullCotree
    (hfull : GridSpanningTreeCotreeDualBoundaryConnectivity (T := T) hT)
    (continuation : LabelledCotreeTransition T → O)
    (hcontinuation : ∀ e, transition (continuation e) = e)
    (hoccurrence : ∀ o, (routingGraph transition).Reachable
      (.inl (.inl o)) (.inl (.inl (continuation (transition o))))) :
    ReachesSplitOuterBoundary transition := by
  let mapBoundary : BoundaryTransitionOccurrence
      (fun e : LabelledCotreeTransition T => e) →
      BoundaryTransitionOccurrence transition := fun b =>
    ⟨continuation b.1, by simpa [hcontinuation] using b.2⟩
  let mapCore : SplitOccurrenceCotreeDualCore
      (fun e : LabelledCotreeTransition T => e) →
      SplitOccurrenceCotreeDualCore transition
    | .inl e => .inl (continuation e)
    | .inr (.inl f) => .inr (.inl f)
    | .inr (.inr b) => .inr (.inr (mapBoundary b))
  let mapRouting : RoutingVertex
      (fun e : LabelledCotreeTransition T => e) → RoutingVertex transition
    | .inl x => .inl (mapCore x)
    | .inr u => .inr u
  let routingHom :
      routingGraph (fun e : LabelledCotreeTransition T => e) →g
        routingGraph transition := {
    toFun := mapRouting
    map_rel' := by
      intro x y hxy
      cases x with
      | inr u =>
          cases y with
          | inl y =>
              cases y with
              | inl e => simp [routingGraph, mapRouting, mapCore, IsOuter] at hxy
              | inr y =>
                  cases y with
                  | inl f => simp [routingGraph, mapRouting, mapCore, IsOuter] at hxy
                  | inr b => simp [routingGraph, mapRouting, mapCore, IsOuter]
          | inr v => simp [routingGraph] at hxy
      | inl x =>
          cases y with
          | inr u =>
              cases x with
              | inl e => simp [routingGraph, mapRouting, mapCore, IsOuter] at hxy
              | inr x =>
                  cases x with
                  | inl f => simp [routingGraph, mapRouting, mapCore, IsOuter] at hxy
                  | inr b => simp [routingGraph, mapRouting, mapCore, IsOuter]
          | inl y =>
              cases x with
              | inl e =>
                  cases y with
                  | inl e' => simp [routingGraph, graph] at hxy
                  | inr y =>
                      cases y with
                      | inl f =>
                          simpa [routingGraph, mapRouting, mapCore, graph, Incident,
                            hcontinuation] using hxy
                      | inr b =>
                          simpa [routingGraph, mapRouting, mapCore, mapBoundary,
                            graph, Incident] using congrArg continuation hxy
              | inr x =>
                  cases y with
                  | inl e =>
                      cases x with
                      | inl f =>
                          simpa [routingGraph, mapRouting, mapCore, graph, Incident,
                            hcontinuation] using hxy
                      | inr b =>
                          simpa [routingGraph, mapRouting, mapCore, mapBoundary,
                            graph, Incident] using congrArg continuation hxy
                  | inr y => simp [routingGraph, graph] at hxy }
  intro x
  cases x with
  | inl o =>
      exact (hoccurrence o).trans (by
        simpa [routingHom, mapRouting, mapCore, hub] using
          (SimpleGraph.Reachable.map routingHom
            (hfull (.inl (transition o)))))
  | inr x =>
      cases x with
      | inl f =>
          simpa [routingHom, mapRouting, mapCore, hub] using
            (SimpleGraph.Reachable.map routingHom
              (hfull (.inr (.inl f))))
      | inr b =>
          exact SimpleGraph.Adj.reachable
            (by simp [routingGraph, hub, IsOuter])

/-- Equal transition labels can be joined through a bounded incident face in a
nondegenerate rectangular grid.  This is the only place where splitting outer
incidences differs from the ordinary barycentric incidence graph. -/
theorem occurrences_reachable_of_transition_eq
    (hm : 2 ≤ m) (hn : 2 ≤ n) {a b : O}
    (hab : transition a = transition b) :
    (routingGraph transition).Reachable (.inl (.inl a)) (.inl (.inl b)) := by
  have hbounded : ∃ f : GridFace m n, f ≠ GridFace.out ∧
      (f = (transition a).1.dualEndpoints.1 ∨
        f = (transition a).1.dualEndpoints.2) := by
    cases hedge : (transition a).1 with
    | horizontal e =>
        by_cases htop : e.row.val = 0
        · exact ⟨GridFace.cell ⟨0, by omega⟩ e.col, by simp,
            Or.inr (by simp [hedge, GridEdge.dualEndpoints,
              horizontalDualEndpoints, htop]; congr 1; omega)⟩
        · exact ⟨GridFace.cell ⟨e.row.val - 1, by omega⟩ e.col, by simp,
            Or.inl (by simp [hedge, GridEdge.dualEndpoints,
              horizontalDualEndpoints, htop])⟩
    | vertical e =>
        by_cases hleft : e.col.val = 0
        · exact ⟨GridFace.cell e.row ⟨0, by omega⟩, by simp,
            Or.inr (by simp [hedge, GridEdge.dualEndpoints,
              verticalDualEndpoints, hleft]; congr 1; omega)⟩
        · exact ⟨GridFace.cell e.row ⟨e.col.val - 1, by omega⟩, by simp,
            Or.inl (by simp [hedge, GridEdge.dualEndpoints,
              verticalDualEndpoints, hleft])⟩
  obtain ⟨f, hfout, hfa⟩ := hbounded
  apply SimpleGraph.Reachable.trans
    (SimpleGraph.Adj.reachable (show (routingGraph transition).Adj
      (.inl (.inl a)) (.inl (.inr (.inl ⟨f, hfout⟩))) by
        exact hfa))
  apply SimpleGraph.Adj.reachable
  change f = (transition b).1.dualEndpoints.1 ∨
    f = (transition b).1.dualEndpoints.2
  simpa [hab] using hfa

/-- Conversely, any non-outer root exhibits the precise missing connectivity
statement.  No boundary edge is added to repair it. -/
theorem not_reaches_splitOuterBoundary_of_nonOuter_root
    [Fintype O] [DecidableEq O]
    {x : SplitOccurrenceCotreeDualCore transition}
    (hroot : x ∈ (forest transition).roots)
    (hnotOuter : ¬IsOuter transition x) :
    ¬(routingGraph transition).Reachable (.inl x) (hub transition) := by
  exact (mem_roots_iff transition x).1 hroot |>.resolve_left hnotOuter

/-- Every private outer incidence is a root, with its occurrence retained. -/
theorem privateOuter_mem_roots [Fintype O] [DecidableEq O]
    (b : BoundaryTransitionOccurrence transition) :
    (.inr (.inr b) : SplitOccurrenceCotreeDualCore transition) ∈
      (forest transition).roots := by
  rw [mem_roots_iff]
  exact Or.inl trivial

/-- A private outer vertex has only its own edge occurrence as a possible
child.  In particular, splitting the outer face cannot create a merger there. -/
theorem child_of_parent_privateOuter [DecidableEq O]
    {x : SplitOccurrenceCotreeDualCore transition}
    (b : BoundaryTransitionOccurrence transition)
    (hparent : parent transition x = some (.inr (.inr b))) :
    x = .inl b.1 := by
  have hadj := parent_adj transition hparent
  cases x with
  | inl o =>
      simp only [graph, Incident] at hadj
      exact congrArg Sum.inl hadj.symm
  | inr x =>
      cases x <;> simp [graph] at hadj

/-- Children of an occurrence vertex are face incidences: either one bounded
face endpoint or that occurrence's private outer endpoint. -/
theorem child_of_parent_occurrence [DecidableEq O]
    {x : SplitOccurrenceCotreeDualCore transition} (o : O)
    (hparent : parent transition x = some (.inl o)) :
    (∃ f : {f : GridFace m n // f ≠ GridFace.out},
      x = .inr (.inl f) ∧
        (f.1 = (transition o).1.dualEndpoints.1 ∨
          f.1 = (transition o).1.dualEndpoints.2)) ∨
      ∃ b : BoundaryTransitionOccurrence transition,
        x = .inr (.inr b) ∧ b.1 = o := by
  have hadj := parent_adj transition hparent
  cases x with
  | inl x => simp [graph] at hadj
  | inr x =>
      cases x with
      | inl f => exact Or.inl ⟨f, rfl, hadj⟩
      | inr b => exact Or.inr ⟨b, rfl, hadj⟩

/-- Children of a bounded-face vertex are exactly incident edge occurrences. -/
theorem child_of_parent_boundedFace [DecidableEq O]
    {x : SplitOccurrenceCotreeDualCore transition}
    (f : {f : GridFace m n // f ≠ GridFace.out})
    (hparent : parent transition x = some (.inr (.inl f))) :
    ∃ o : O, x = .inl o ∧
      (f.1 = (transition o).1.dualEndpoints.1 ∨
        f.1 = (transition o).1.dualEndpoints.2) := by
  have hadj := parent_adj transition hparent
  cases x with
  | inl o => exact ⟨o, rfl, hadj⟩
  | inr x => cases x <;> simp [graph] at hadj

theorem privateOuter_childCount_le_one [Fintype O] [DecidableEq O]
    (b : BoundaryTransitionOccurrence transition) :
    (forest transition).childCount (.inr (.inr b)) ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  rw [ParentForest.children, Finset.mem_filter] at hx hy
  exact (child_of_parent_privateOuter transition b hx.2).trans
    (child_of_parent_privateOuter transition b hy.2).symm

/-- Every core merger is either an edge-occurrence vertex or a bounded-face
vertex.  Private outer occurrences are roots but never branch vertices. -/
theorem merger_is_occurrence_or_boundedFace [Fintype O] [DecidableEq O]
    (x : SplitOccurrenceCotreeDualCore transition)
    (hx : x ∈ (forest transition).mergers) :
    (∃ o, x = .inl o) ∨
      ∃ f : {f : GridFace m n // f ≠ GridFace.out}, x = .inr (.inl f) := by
  cases x with
  | inl o => exact Or.inl ⟨o, rfl⟩
  | inr x =>
      cases x with
      | inl f => exact Or.inr ⟨f, rfl⟩
      | inr b =>
          rw [ParentForest.mem_mergers] at hx
          have hle := privateOuter_childCount_le_one transition b
          omega

end SplitOccurrenceCotreeDualCore

/-! ## Occurrence-split outer forest with private start leaves -/

/-- Final split carrier.  Starts remain private leaves, while each occurrence
of the outer face remains a private root in the core. -/
def SplitOccurrenceLabelledCotreeDualCarrier {EdgeOccurrence : Type*}
    (transition : EdgeOccurrence → LabelledCotreeTransition T) (Start : Type*) :=
  Start ⊕ SplitOccurrenceCotreeDualCore transition

namespace SplitOccurrenceLabelledCotreeDualCarrier

variable {Start EdgeOccurrence : Type*}
  [Fintype Start] [DecidableEq Start]
  [Fintype EdgeOccurrence] [DecidableEq EdgeOccurrence]
  (transition : EdgeOccurrence → LabelledCotreeTransition T)
  (startEdge : Start → EdgeOccurrence)

noncomputable instance carrierFintype : Fintype
    (SplitOccurrenceLabelledCotreeDualCarrier transition Start) := by
  unfold SplitOccurrenceLabelledCotreeDualCarrier
  infer_instance

noncomputable instance carrierDecidableEq : DecidableEq
    (SplitOccurrenceLabelledCotreeDualCarrier transition Start) := by
  unfold SplitOccurrenceLabelledCotreeDualCarrier
  infer_instance

/-- Attach every start to its occurrence vertex over a chosen core parent
tie-breaking.  The private-leaf layer is independent of how equal-length core
parents are ordered. -/
noncomputable def forestWithTieBreaking
    (choice : SplitOccurrenceCotreeDualCore.ParentTieBreaking transition) : ParentForest
    (SplitOccurrenceLabelledCotreeDualCarrier transition Start) where
  parent
    | .inl start => some (.inr (.inl (startEdge start)))
    | .inr x => (choice.parent x).map Sum.inr
  rank
    | .inl start =>
        (choice.forest).rank
          (.inl (startEdge start)) + 1
    | .inr x => (choice.forest).rank x
  rank_parent := by
    intro v w hparent
    cases v with
    | inl start =>
        simp only [Option.some.injEq] at hparent
        subst w
        simp
    | inr x =>
        cases hcore : choice.parent x with
        | none => simp [hcore] at hparent
        | some y =>
            simp [hcore] at hparent
            subst w
            exact choice.dist_parent_lt hcore

/-- Canonical split carrier forest, retaining the previous arbitrary
shortest-path tie-breaking as an explicit choice. -/
noncomputable def forest : ParentForest
    (SplitOccurrenceLabelledCotreeDualCarrier transition Start) :=
  forestWithTieBreaking transition startEdge
    (SplitOccurrenceCotreeDualCore.shortestPathTieBreaking transition)

theorem no_parent_is_privateLeaf
    (x : SplitOccurrenceLabelledCotreeDualCarrier transition Start)
    (start : Start) : (forest transition startEdge).parent x ≠ some (.inl start) := by
  cases x <;> simp [forest, forestWithTieBreaking]

theorem privateLeaf_mem_leaves (start : Start) :
    (.inl start : SplitOccurrenceLabelledCotreeDualCarrier transition Start) ∈
      (forest transition startEdge).leaves := by
  classical
  simp only [ParentForest.leaves, Finset.mem_filter, Finset.mem_univ, true_and,
    ParentForest.childCount]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact no_parent_is_privateLeaf transition startEdge x start
    (Finset.mem_filter.mp hx).2

/-- A private start has no children and therefore cannot itself be a merger. -/
theorem privateLeaf_not_mem_mergers (start : Start) :
    (.inl start : SplitOccurrenceLabelledCotreeDualCarrier transition Start) ∉
      (forest transition startEdge).mergers := by
  intro h
  rw [ParentForest.mem_mergers] at h
  have hleaf := privateLeaf_mem_leaves transition startEdge start
  simp [ParentForest.leaves] at hleaf
  omega

/-- Private start leaves do not create roots. The roots are exactly private
boundary occurrences and core vertices in components not reaching the hub. -/
theorem mem_roots_iff
    (x : SplitOccurrenceLabelledCotreeDualCarrier transition Start) :
    x ∈ (forest transition startEdge).roots ↔
      (∃ b : BoundaryTransitionOccurrence transition,
        x = .inr (.inr (.inr b))) ∨
      (∃ y : SplitOccurrenceCotreeDualCore transition,
        x = .inr y ∧
          ¬(SplitOccurrenceCotreeDualCore.routingGraph transition).Reachable
            (.inl y) (SplitOccurrenceCotreeDualCore.hub transition)) := by
  classical
  cases x with
  | inl start => simp [ParentForest.roots, forest, forestWithTieBreaking]
  | inr y =>
      rw [show (.inr y : SplitOccurrenceLabelledCotreeDualCarrier transition Start) ∈
          (forest transition startEdge).roots ↔
          y ∈ (SplitOccurrenceCotreeDualCore.forest transition).roots by
        simp [ParentForest.roots, forest, forestWithTieBreaking,
          SplitOccurrenceCotreeDualCore.shortestPathTieBreaking,
          SplitOccurrenceCotreeDualCore.forest]]
      rw [SplitOccurrenceCotreeDualCore.mem_roots_iff]
      constructor
      · rintro (houter | hunreachable)
        · cases y with
          | inl o => exact houter.elim
          | inr y =>
              cases y with
              | inl f => exact houter.elim
              | inr b => exact Or.inl ⟨b, rfl⟩
        · exact Or.inr ⟨y, rfl, hunreachable⟩
      · rintro (⟨b, h⟩ | ⟨z, h, hunreachable⟩)
        · cases h
          exact Or.inl trivial
        · cases h
          exact Or.inr hunreachable

noncomputable def startLeafEmbedding : Start ↪
    ↥((forest transition startEdge).leaves) where
  toFun start := ⟨.inl start, privateLeaf_mem_leaves transition startEdge start⟩
  inj' := by
    intro a b hab
    exact Sum.inl.inj (congrArg (fun x => x.1) hab)

end SplitOccurrenceLabelledCotreeDualCarrier

end GridGraphs
