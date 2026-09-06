import GridGraphs.GridBoundaryCycle
import GridGraphs.GridCotreePorts
import GridGraphs.NoncrossingShoreChannels

/-!
# Split outer ports for a grid cotree

The unbounded grid face has one geometrically distinct incidence for every
supported boundary side.  Corners therefore contribute two ports.  This file
constructs those ports as four disjoint side-labelled types and proves that
they are exactly the abstract `BoundarySector` ledger.

`GridCotreeSplitFace` is the finite carrier obtained by replacing the single
face `GridFace.out` with these ports.  No adjacency, connectivity, or tree
claim is made: assigning cotree edges to the split ports requires additional
rotation-system data not present in the current combinatorial dual API.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The four geometric sides at which the unbounded face meets the grid. -/
inductive OuterBoundarySide
  | top
  | bottom
  | left
  | right
  deriving DecidableEq

instance : Fintype OuterBoundarySide where
  elems := {.top, .bottom, .left, .right}
  complete side := by cases side <;> simp

/-- Geometric outer incidences based at vertices of `U`.  The nested sum keeps
the four side copies disjoint, so a supported corner has two distinct ports. -/
def OuterBoundaryPort {m n : Nat} (U : Finset (GridVertex m n)) :=
  ↥(U.filter fun v => v.1.val = 0) ⊕
    (↥(U.filter fun v => v.1.val + 1 = m) ⊕
      (↥(U.filter fun v => v.2.val = 0) ⊕
        ↥(U.filter fun v => v.2.val + 1 = n)))

noncomputable instance outerBoundaryPortFintype {m n : Nat}
    (U : Finset (GridVertex m n)) : Fintype (OuterBoundaryPort U) := by
  unfold OuterBoundaryPort
  infer_instance

namespace OuterBoundaryPort

/-- A supported boundary vertex with an incident side determines the
corresponding split outer port. -/
def ofSupportedVertexSide {m n : Nat} {U : Finset (GridVertex m n)}
    (v : GridVertex m n) (hv : v ∈ U) (side : OuterBoundarySide)
    (hside : match side with
      | .top => v.1.val = 0
      | .bottom => v.1.val + 1 = m
      | .left => v.2.val = 0
      | .right => v.2.val + 1 = n) : OuterBoundaryPort U := by
  cases side with
  | top => exact .inl ⟨v, Finset.mem_filter.mpr ⟨hv, hside⟩⟩
  | bottom => exact .inr (.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hside⟩⟩)
  | left => exact .inr (.inr (.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hside⟩⟩))
  | right => exact .inr (.inr (.inr ⟨v, Finset.mem_filter.mpr ⟨hv, hside⟩⟩))

/-- The supported boundary vertex carrying an outer port. -/
def vertex {m n : Nat} {U : Finset (GridVertex m n)} :
    OuterBoundaryPort U → GridVertex m n
  | .inl p => p.1
  | .inr (.inl p) => p.1
  | .inr (.inr (.inl p)) => p.1
  | .inr (.inr (.inr p)) => p.1

/-- The geometric side represented by an outer port. -/
def side {m n : Nat} {U : Finset (GridVertex m n)} :
    OuterBoundaryPort U → OuterBoundarySide
  | .inl _ => .top
  | .inr (.inl _) => .bottom
  | .inr (.inr (.inl _)) => .left
  | .inr (.inr (.inr _)) => .right

/-- A split outer port is determined by its supported vertex and side. -/
theorem eq_of_vertex_eq_of_side_eq {m n : Nat} {U : Finset (GridVertex m n)}
    {p q : OuterBoundaryPort U} (hv : p.vertex = q.vertex)
    (hs : p.side = q.side) : p = q := by
  rcases p with p | p | p | p <;>
    rcases q with q | q | q | q <;> simp [side] at hs
  all_goals congr; exact Subtype.ext hv

@[simp] theorem vertex_ofSupportedVertexSide
    {m n : Nat} {U : Finset (GridVertex m n)}
    (v : GridVertex m n) (hv : v ∈ U) (side : OuterBoundarySide)
    (hside : match side with
      | .top => v.1.val = 0
      | .bottom => v.1.val + 1 = m
      | .left => v.2.val = 0
      | .right => v.2.val + 1 = n) :
    (ofSupportedVertexSide v hv side hside).vertex = v := by
  cases side <;> rfl

@[simp] theorem side_ofSupportedVertexSide
    {m n : Nat} {U : Finset (GridVertex m n)}
    (v : GridVertex m n) (hv : v ∈ U) (side : OuterBoundarySide)
    (hside : match side with
      | .top => v.1.val = 0
      | .bottom => v.1.val + 1 = m
      | .left => v.2.val = 0
      | .right => v.2.val + 1 = n) :
    (ofSupportedVertexSide v hv side hside).side = side := by
  cases side <;> rfl

/-- Every outer port is based in `U`. -/
theorem vertex_mem {m n : Nat} {U : Finset (GridVertex m n)}
    (p : OuterBoundaryPort U) : p.vertex ∈ U := by
  rcases p with p | p
  · exact (Finset.mem_filter.mp p.2).1
  · rcases p with p | p
    · exact (Finset.mem_filter.mp p.2).1
    · rcases p with p | p
      · exact (Finset.mem_filter.mp p.2).1
      · exact (Finset.mem_filter.mp p.2).1

/-- The side label records the corresponding missing boundary incidence. -/
theorem side_incidence {m n : Nat} {U : Finset (GridVertex m n)}
    (p : OuterBoundaryPort U) :
    match p.side with
    | .top => p.vertex.1.val = 0
    | .bottom => p.vertex.1.val + 1 = m
    | .left => p.vertex.2.val = 0
    | .right => p.vertex.2.val + 1 = n := by
  rcases p with p | p
  · exact (Finset.mem_filter.mp p.2).2
  · rcases p with p | p
    · exact (Finset.mem_filter.mp p.2).2
    · rcases p with p | p
      · exact (Finset.mem_filter.mp p.2).2
      · exact (Finset.mem_filter.mp p.2).2

end OuterBoundaryPort

/-- The geometric outer ports have exactly the boundary-deficiency
multiplicity, including two distinct incidences at each supported corner. -/
theorem card_outerBoundaryPort {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : Finset (GridVertex m n)) :
    Fintype.card (OuterBoundaryPort U) = boundaryDeficiencySum m n U := by
  classical
  simp only [OuterBoundaryPort, Fintype.card_sum, Fintype.card_coe]
  rw [boundaryDeficiencySum_eq_four_side_card hm hn]
  omega

/-- Exact identification of geometric side incidences with the abstract
boundary-sector ledger. -/
noncomputable def outerBoundaryPortEquivBoundarySector {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (U : Finset (GridVertex m n)) :
    OuterBoundaryPort U ≃ BoundarySector U :=
  Fintype.equivOfCardEq
    ((card_outerBoundaryPort hm hn U).trans (card_boundarySector U).symm)

/-- Outer ports of the cotree of `T`: precisely the supported missing
boundary incidences. -/
def GridCotreeOuterPort {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  OuterBoundaryPort (supportFinset (gridGraph m n \ T))

noncomputable instance gridCotreeOuterPortFintype {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :
    Fintype (GridCotreeOuterPort T) := by
  unfold GridCotreeOuterPort
  infer_instance

/-- Finite face carrier in which the one unbounded face is replaced by its
distinct cotree-supported boundary incidences. -/
def GridCotreeSplitFace {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  {f : GridFace m n // f ≠ GridFace.out} ⊕ GridCotreeOuterPort T

/-- For a spanning grid tree, split outer ports are exactly its supported
`BoundarySector`s. -/
noncomputable def gridCotreeOuterPortEquivBoundarySector {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (_hT : IsSpanningSubtree (gridGraph m n) T) :
    GridCotreeOuterPort T ≃
      BoundarySector (supportFinset (gridGraph m n \ T)) :=
  outerBoundaryPortEquivBoundarySector hm hn _

/-- Exact split-outer port count for a spanning grid tree. -/
theorem card_gridCotreeOuterPort_eq_boundaryDeficiencySum {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (_hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (GridCotreeOuterPort T) =
      boundaryDeficiencySum m n (supportFinset (gridGraph m n \ T)) :=
  card_outerBoundaryPort hm hn _

end GridGraphs
