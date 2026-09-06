import GridGraphs.Geometry.GridCotreeSplitOuter

/-!
# Outer cotree ports on the tree contour

An outer port determines a missing outward compass direction at its boundary
vertex.  The retained tree directions at that vertex are nonempty, so there is
a unique cyclic gap between consecutive retained directions containing the
outward direction.  We represent that contour transition by the retained dart
at the start of the gap.  Its reverse is the arriving contour dart and its
contour successor leaves in the direction at the other end of the gap.

The dart alone need not distinguish the two ports at a corner.  The refined
occurrence below therefore retains both the dart and the crossed direction.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace GridDirection

/-- `x` occurs strictly after `a` and strictly before `b` while moving
clockwise.  When `a = b`, this means the nontrivial full clockwise circuit. -/
def StrictClockwiseBetween (a b x : GridDirection) : Prop :=
  (x = a.clockwise ∧
      (b = a.clockwise.clockwise ∨
       b = a.clockwise.clockwise.clockwise ∨ b = a)) ∨
  (x = a.clockwise.clockwise ∧
      (b = a.clockwise.clockwise.clockwise ∨ b = a)) ∨
  (x = a.clockwise.clockwise.clockwise ∧ b = a)

/-- The clockwise turn from an occupied direction to its next occupied
direction sweeps strictly across `x`. -/
def TurnCrosses (S : Finset GridDirection) (a x : GridDirection) : Prop :=
  a ∈ S ∧ x ∉ S ∧ StrictClockwiseBetween a (a.nextIn S) x

private def gapStartCandidate (S : Finset GridDirection)
    (x : GridDirection) : GridDirection :=
  if x.clockwise.clockwise.clockwise ∈ S then
    x.clockwise.clockwise.clockwise
  else if x.clockwise.clockwise ∈ S then x.clockwise.clockwise
  else x.clockwise

/-- Every direction outside a nonempty set of compass directions lies in one
unique cyclic gap between consecutive members of the set. -/
theorem existsUnique_turnCrosses (S : Finset GridDirection) (hS : S.Nonempty)
    {x : GridDirection} (hx : x ∉ S) :
    ∃! a, TurnCrosses S a x := by
  obtain ⟨z, hz⟩ := hS
  have hsome : GridDirection.north ∈ S ∨ GridDirection.east ∈ S ∨
      GridDirection.south ∈ S ∨ GridDirection.west ∈ S := by
    fin_cases z <;> simp_all
  by_cases hn : GridDirection.north ∈ S <;>
    by_cases he : GridDirection.east ∈ S <;>
    by_cases hs : GridDirection.south ∈ S <;>
    by_cases hw : GridDirection.west ∈ S
  all_goals
    refine ⟨gapStartCandidate S x, ?_, ?_⟩
    · fin_cases x <;>
        simp_all [gapStartCandidate, TurnCrosses,
          StrictClockwiseBetween, nextIn, clockwise]
    · intro y hy
      fin_cases x <;> fin_cases y <;>
        simp_all [gapStartCandidate, TurnCrosses,
          StrictClockwiseBetween, nextIn, clockwise]

/-- Start of the unique occupied cyclic gap containing `x`. -/
noncomputable def gapStart (S : Finset GridDirection) (hS : S.Nonempty)
    (x : GridDirection) (hx : x ∉ S) : GridDirection :=
  (existsUnique_turnCrosses S hS hx).exists.choose

theorem gapStart_turnCrosses (S : Finset GridDirection) (hS : S.Nonempty)
    (x : GridDirection) (hx : x ∉ S) :
    TurnCrosses S (gapStart S hS x hx) x :=
  (existsUnique_turnCrosses S hS hx).exists.choose_spec

theorem turnCrosses_eq_gapStart (S : Finset GridDirection) (hS : S.Nonempty)
    (x : GridDirection) (hx : x ∉ S) {a : GridDirection}
    (ha : TurnCrosses S a x) : a = gapStart S hS x hx :=
  (existsUnique_turnCrosses S hS hx).unique ha
    (gapStart_turnCrosses S hS x hx)

end GridDirection

namespace OuterBoundarySide

/-- Compass direction of the outward boundary stub represented by a side. -/
def outwardDirection : OuterBoundarySide → GridDirection
  | .top => .north
  | .bottom => .south
  | .left => .west
  | .right => .east

theorem outwardDirection_injective : Function.Injective outwardDirection := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [outwardDirection]

end OuterBoundarySide

namespace OuterBoundaryPort

/-- Outward compass direction of a split outer port. -/
def outwardDirection {m n : Nat} {U : Finset (GridVertex m n)}
    (p : OuterBoundaryPort U) : GridDirection :=
  p.side.outwardDirection

/-- The outward stub of a boundary port leaves the rectangular grid. -/
theorem gridNeighbor?_outwardDirection_eq_none {m n : Nat}
    {U : Finset (GridVertex m n)} (p : OuterBoundaryPort U) :
    gridNeighbor? p.vertex p.outwardDirection = none := by
  have h := p.side_incidence
  cases hs : p.side <;>
    simp only [hs] at h <;>
    simp [outwardDirection, hs, OuterBoundarySide.outwardDirection, gridNeighbor?, h]

/-- A split outer port is determined by its vertex and side label. -/
theorem ext {m n : Nat} {U : Finset (GridVertex m n)}
    {p q : OuterBoundaryPort U} (hv : p.vertex = q.vertex)
    (hs : p.side = q.side) : p = q := by
  rcases p with p | p
  · rcases q with q | q
    · exact congrArg Sum.inl (Subtype.ext hv)
    · rcases q with q | q
      · simp [side] at hs
      · rcases q with q | q <;> simp [side] at hs
  · rcases p with p | p
    · rcases q with q | q
      · simp [side] at hs
      · rcases q with q | q
        · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext hv)
        · rcases q with q | q <;> simp [side] at hs
    · rcases p with p | p
      · rcases q with q | q
        · simp [side] at hs
        · rcases q with q | q
          · simp [side] at hs
          · rcases q with q | q
            · exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) (Subtype.ext hv)
            · simp [side] at hs
      · rcases q with q | q
        · simp [side] at hs
        · rcases q with q | q
          · simp [side] at hs
          · rcases q with q | q
            · simp [side] at hs
            · exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inr) (Subtype.ext hv)

end OuterBoundaryPort

namespace GridCotreeOuterPort

variable {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]

/-- Retained tree directions at the vertex carrying an outer port are
nonempty for a nontrivial spanning square grid. -/
theorem directionsAt_nonempty (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) (p : GridCotreeOuterPort T) :
    (GridDirectionalDart.directionsAt (T := T) p.vertex).Nonempty := by
  have hdegree : 0 < T.degree p.vertex :=
    tree_degree_pos (by nlinarith) hT p.vertex
  obtain ⟨w, hvw⟩ := (T.degree_pos_iff_exists_adj p.vertex).mp hdegree
  obtain ⟨d, hdsource, _⟩ := GridDirectionalDart.exists_of_adj hT.le hvw
  refine ⟨d.direction, GridDirectionalDart.mem_directionsAt.mpr ?_⟩
  exact ⟨d.target, by simpa only [hdsource] using d.step,
    by simpa only [hdsource] using d.adj⟩

/-- An outward boundary direction is not a retained tree direction. -/
theorem outwardDirection_notMem_directionsAt
    (p : GridCotreeOuterPort T) :
    p.outwardDirection ∉ GridDirectionalDart.directionsAt (T := T) p.vertex := by
  intro hp
  obtain ⟨w, hstep, _⟩ := GridDirectionalDart.mem_directionsAt.mp hp
  rw [p.gridNeighbor?_outwardDirection_eq_none] at hstep
  contradiction

end GridCotreeOuterPort

/-- A local contour occurrence refined by the direction swept across. -/
structure GridOuterPortContourOccurrence {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] where
  dart : GridDirectionalDart T
  crossedDirection : GridDirection
  crosses : GridDirection.TurnCrosses
    (GridDirectionalDart.directionsAt (T := T) dart.source)
    dart.direction crossedDirection

namespace GridOuterPortContourOccurrence

variable {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]

theorem ext {a b : GridOuterPortContourOccurrence T}
    (hdart : a.dart = b.dart)
    (hdirection : a.crossedDirection = b.crossedDirection) : a = b := by
  cases a
  cases b
  simp_all

end GridOuterPortContourOccurrence

namespace GridCotreeOuterPort

variable {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]

/-- The retained dart at the start of the unique cyclic gap containing the
port's outward boundary stub. -/
noncomputable def contourDart (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) : GridDirectionalDart T := by
  let S := GridDirectionalDart.directionsAt (T := T) p.vertex
  let a := GridDirection.gapStart S (directionsAt_nonempty hn hT p)
    p.outwardDirection (outwardDirection_notMem_directionsAt p)
  exact GridDirectionalDart.ofDirectionMem (T := T) p.vertex a
    (GridDirection.gapStart_turnCrosses S (directionsAt_nonempty hn hT p)
      p.outwardDirection (outwardDirection_notMem_directionsAt p)).1

@[simp] theorem contourDart_source (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) :
    (contourDart hn hT p).source = p.vertex := rfl

/-- The selected local contour turn sweeps across the port's outward stub. -/
theorem contourDart_crosses (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) :
    GridDirection.TurnCrosses
      (GridDirectionalDart.directionsAt (T := T) p.vertex)
      (contourDart hn hT p).direction p.outwardDirection := by
  exact GridDirection.gapStart_turnCrosses _ (directionsAt_nonempty hn hT p) _
    (outwardDirection_notMem_directionsAt p)

/-- In the existing contour permutation, the reverse of the selected based
dart arrives at the port vertex and its successor leaves at the other endpoint
of the selected clockwise gap. -/
theorem contourSucc_reverse_direction (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) :
    ((contourDart hn hT p).reverse.contourSucc).direction =
      (contourDart hn hT p).direction.nextIn
        (GridDirectionalDart.directionsAt (T := T) p.vertex) := by
  simp [GridDirectionalDart.reverse]

/-- No other retained dart based at the port vertex starts a turn crossing the
same outward stub. -/
theorem contourDart_unique (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) {d : GridDirectionalDart T}
    (hsource : d.source = p.vertex)
    (hcrosses : GridDirection.TurnCrosses
      (GridDirectionalDart.directionsAt (T := T) p.vertex)
      d.direction p.outwardDirection) :
    d = contourDart hn hT p := by
  apply GridDirectionalDart.ext hsource
  exact GridDirection.turnCrosses_eq_gapStart _ (directionsAt_nonempty hn hT p) _
    (outwardDirection_notMem_directionsAt p) hcrosses

/-- The selected dart together with the crossed outward direction. -/
noncomputable def contourOccurrence (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) : GridOuterPortContourOccurrence T where
  dart := contourDart hn hT p
  crossedDirection := p.outwardDirection
  crosses := by simpa using contourDart_crosses hn hT p

/-- Refinement by the crossed direction restores injectivity lost by plain
darts at corners. -/
theorem contourOccurrence_injective (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    Function.Injective (contourOccurrence hn hT) := by
  intro p q hpq
  apply OuterBoundaryPort.ext
  · have hdart := congrArg GridOuterPortContourOccurrence.dart hpq
    simpa only [contourOccurrence, contourDart_source] using
      congrArg GridDirectionalDart.source hdart
  · apply OuterBoundarySide.outwardDirection_injective
    simpa only [contourOccurrence, OuterBoundaryPort.outwardDirection] using
      congrArg GridOuterPortContourOccurrence.crossedDirection hpq

end GridCotreeOuterPort

end GridGraphs
