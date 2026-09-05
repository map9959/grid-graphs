import GridGraphs.GridCellBoundaryEdges

/-!
# Retained support-edge pass-through

An occurrence entering a retained tree edge whose two primal endpoints lie in
cotree support can continue to the other incident grid face.  The occurrence
label and the raw internal-edge resource are retained; only the entered face is
changed.  Ordered `GridEdge` primal and dual endpoints handle horizontal,
vertical, boundary, and interior edges uniformly.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

namespace GridEdge

/-- The other ordered dual endpoint of an edge, relative to an incident face. -/
def oppositeFace {m n : Nat} (edge : GridEdge m n) (entered : GridFace m n) :
    GridFace m n :=
  if entered = edge.dualEndpoints.1 then
    edge.dualEndpoints.2
  else
    edge.dualEndpoints.1

theorem hasDualEndpoints_entered_oppositeFace {m n : Nat}
    (edge : GridEdge m n) (entered : GridFace m n)
    (hincident : entered = edge.dualEndpoints.1 ∨
      entered = edge.dualEndpoints.2) :
    HasDualEndpoints edge.dualEndpoints entered (edge.oppositeFace entered) := by
  rcases hincident with hfirst | hsecond
  · subst entered
    exact Or.inl ⟨rfl, by simp [oppositeFace]⟩
  · subst entered
    by_cases hsame : edge.dualEndpoints.2 = edge.dualEndpoints.1
    · exact Or.inr ⟨rfl, by simp [oppositeFace, hsame]⟩
    · exact Or.inr ⟨rfl, by simp [oppositeFace, hsame]⟩

/-- In a nondegenerate rectangle, every coordinate edge has two distinct
incident faces.  This includes boundary edges, whose exterior endpoint is
`GridFace.out`. -/
theorem dualEndpoints_ne {m n : Nat} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n)
    (edge : GridEdge m n) :
    edge.dualEndpoints.1 ≠ edge.dualEndpoints.2 := by
  cases edge with
  | horizontal edge =>
      simp only [dualEndpoints_horizontal]
      intro heq
      by_cases htop : edge.row.val = 0
      · by_cases hbottom : edge.row.val + 1 = m
        · omega
        · simp [horizontalDualEndpoints, htop] at heq
          omega
      · by_cases hbottom : edge.row.val + 1 = m
        · simp [horizontalDualEndpoints, htop, hbottom] at heq
        · simp [horizontalDualEndpoints, htop, hbottom, Fin.ext_iff] at heq
          omega
  | vertical edge =>
      simp only [dualEndpoints_vertical]
      intro heq
      by_cases hleft : edge.col.val = 0
      · by_cases hright : edge.col.val + 1 = n
        · omega
        · simp [verticalDualEndpoints, hleft] at heq
          omega
      · by_cases hright : edge.col.val + 1 = n
        · simp [verticalDualEndpoints, hleft, hright] at heq
        · simp [verticalDualEndpoints, hleft, hright, Fin.ext_iff] at heq
          omega

theorem oppositeFace_ne {m n : Nat} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n)
    (edge : GridEdge m n) (entered : GridFace m n)
    (hincident : entered = edge.dualEndpoints.1 ∨
      entered = edge.dualEndpoints.2) :
    edge.oppositeFace entered ≠ entered := by
  have hne := edge.dualEndpoints_ne hm2 hn2
  rcases hincident with hfirst | hsecond
  · subst entered
    simpa [oppositeFace] using hne.symm
  · have hnotfirst : edge.dualEndpoints.2 ≠ edge.dualEndpoints.1 := hne.symm
    subst entered
    simpa [oppositeFace, hnotfirst] using hne

end GridEdge

/-- Occurrence-labelled entry at one face of one retained support-support tree
edge.  `raw_eq` uses the exact primal endpoint API to identify the coordinate
edge with the single raw `internalEdgeFinset` resource. -/
structure RetainedSupportEdgePassThroughState
    {m n : Nat} (Origin : Type*)
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] where
  origin : Origin
  enteredFace : GridFace m n
  enteredEdge : GridEdge m n
  raw : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T)))
  raw_eq : raw.1 = enteredEdge.primalSym2
  entered_incident : enteredFace = enteredEdge.dualEndpoints.1 ∨
    enteredFace = enteredEdge.dualEndpoints.2

namespace RetainedSupportEdgePassThroughState

variable {m n : Nat} {Origin : Type*}
  {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- Both exact primal endpoints are in cotree support, as encoded by the raw
internal tree-edge resource. -/
theorem primalEndpoints_supported
    (state : RetainedSupportEdgePassThroughState Origin T) :
    state.enteredEdge.primalEndpoints.1 ∈
        supportFinset (gridGraph m n \ T) ∧
      state.enteredEdge.primalEndpoints.2 ∈
        supportFinset (gridGraph m n \ T) := by
  have hall := ((mem_internalEdgeFinset T
    (supportFinset (gridGraph m n \ T)) state.raw.1).mp state.raw.2).2
  constructor
  · apply hall state.enteredEdge.primalEndpoints.1
    rw [state.raw_eq, GridEdge.primalSym2, Sym2.mem_iff]
    exact Or.inl rfl
  · apply hall state.enteredEdge.primalEndpoints.2
    rw [state.raw_eq, GridEdge.primalSym2, Sym2.mem_iff]
    exact Or.inr rfl

/-- The exact primal endpoints form an edge of the retained tree. -/
theorem primalEndpoints_treeAdjacent
    (state : RetainedSupportEdgePassThroughState Origin T) :
    T.Adj state.enteredEdge.primalEndpoints.1
      state.enteredEdge.primalEndpoints.2 := by
  have hedge := ((mem_internalEdgeFinset T
    (supportFinset (gridGraph m n \ T)) state.raw.1).mp state.raw.2).1
  rw [SimpleGraph.mem_edgeFinset] at hedge
  simpa [state.raw_eq, GridEdge.primalSym2] using hedge

/-- Continue the same occurrence and raw edge to the opposite incident face. -/
def passThrough (state : RetainedSupportEdgePassThroughState Origin T) :
    RetainedSupportEdgePassThroughState Origin T where
  origin := state.origin
  enteredFace := state.enteredEdge.oppositeFace state.enteredFace
  enteredEdge := state.enteredEdge
  raw := state.raw
  raw_eq := state.raw_eq
  entered_incident := by
    have h := GridEdge.hasDualEndpoints_entered_oppositeFace state.enteredEdge
      state.enteredFace state.entered_incident
    exact h.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

@[simp] theorem passThrough_origin
    (state : RetainedSupportEdgePassThroughState Origin T) :
    state.passThrough.origin = state.origin := rfl

@[simp] theorem passThrough_enteredEdge
    (state : RetainedSupportEdgePassThroughState Origin T) :
    state.passThrough.enteredEdge = state.enteredEdge := rfl

@[simp] theorem passThrough_raw
    (state : RetainedSupportEdgePassThroughState Origin T) :
    state.passThrough.raw = state.raw := rfl

/-- The continuation really enters the opposite, rather than the same, face. -/
theorem passThrough_face_ne (hm2 : 2 ≤ m) (hn2 : 2 ≤ n)
    (state : RetainedSupportEdgePassThroughState Origin T) :
    state.passThrough.enteredFace ≠ state.enteredFace :=
  GridEdge.oppositeFace_ne hm2 hn2 state.enteredEdge state.enteredFace
    state.entered_incident

/-- Exact opposite-face validity in the unordered dual-endpoint API. -/
theorem passThrough_hasDualEndpoints
    (state : RetainedSupportEdgePassThroughState Origin T) :
    HasDualEndpoints state.enteredEdge.dualEndpoints state.enteredFace
      state.passThrough.enteredFace :=
  GridEdge.hasDualEndpoints_entered_oppositeFace state.enteredEdge
    state.enteredFace state.entered_incident

end RetainedSupportEdgePassThroughState

end GridGraphs
