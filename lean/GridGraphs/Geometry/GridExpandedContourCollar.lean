import GridGraphs.Geometry.GridExpandedContourTrace

/-!
# A doubled-grid collar for expanded contour traces

Grid vertices are placed at fourfold coordinates with a one-unit collar.
Compass slots become sector corners around those centers.  An occupied move
follows one offset side of its retained edge, while an unoccupied move follows
a clockwise corner turn.  Reverse edge traversals use opposite offset sides.
This realizes every local expanded successor, including outward boundary
slots, as a continuous walk in a finite rectangular grid.
-/

namespace GridGraphs

open SimpleGraph

namespace GridExpandedContour

/-- Side length of the fourfold coordinate carrier with one unit beyond every
slot sector. -/
def collarSize (n : Nat) : Nat := 4 * n + 3

/-- Center representing an original grid vertex. -/
def collarCenter {m n : Nat} (v : GridVertex m n) :
    GridVertex (collarSize m) (collarSize n) :=
  (⟨4 * v.1.val + 2, by simp [collarSize]⟩,
    ⟨4 * v.2.val + 2, by simp [collarSize]⟩)

/-- Cardinal midpoint representing a compass slot.  Boundary outward slots
land in the added collar rather than outside the carrier. -/
def slotPoint {m n : Nat} (s : GridCompassSlot m n) :
    GridVertex (collarSize m) (collarSize n) :=
  match s.2 with
  | .north =>
      (⟨4 * s.1.1.val + 1, by simp [collarSize]; omega⟩,
        ⟨4 * s.1.2.val + 1, by simp [collarSize]; omega⟩)
  | .east =>
      (⟨4 * s.1.1.val + 1, by simp [collarSize]; omega⟩,
        ⟨4 * s.1.2.val + 3, by simp [collarSize]⟩)
  | .south =>
      (⟨4 * s.1.1.val + 3, by simp [collarSize]⟩,
        ⟨4 * s.1.2.val + 3, by simp [collarSize]⟩)
  | .west =>
      (⟨4 * s.1.1.val + 3, by simp [collarSize]⟩,
        ⟨4 * s.1.2.val + 1, by simp [collarSize]; omega⟩)

/-- Distinct expanded slots have distinct offset-sector points. -/
theorem slotPoint_injective {m n : Nat} :
    Function.Injective (@slotPoint m n) := by
  rintro ⟨v, d⟩ ⟨w, e⟩ h
  fin_cases d <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [slotPoint] at hr hc
    first
    | omega
    | congr 1
      apply Prod.ext <;> apply Fin.ext <;> omega

/-- Corner between a slot direction and its clockwise successor. -/
def turnCorner {m n : Nat} (v : GridVertex m n) (d : GridDirection) :
    GridVertex (collarSize m) (collarSize n) :=
  match d with
  | .north =>
      (⟨4 * v.1.val + 1, by simp [collarSize]; omega⟩,
        ⟨4 * v.2.val + 2, by simp [collarSize]⟩)
  | .east =>
      (⟨4 * v.1.val + 2, by simp [collarSize]⟩,
        ⟨4 * v.2.val + 3, by simp [collarSize]⟩)
  | .south =>
      (⟨4 * v.1.val + 3, by simp [collarSize]⟩,
        ⟨4 * v.2.val + 2, by simp [collarSize]⟩)
  | .west =>
      (⟨4 * v.1.val + 2, by simp [collarSize]⟩,
        ⟨4 * v.2.val + 1, by simp [collarSize]; omega⟩)

/-- Centerline point of the geometric corridor carrying a retained grid edge. -/
def edgeCorridorCenter {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    (d : GridDirectionalDart T) :
    GridVertex (collarSize m) (collarSize n) :=
  match d.direction with
  | .north =>
      (⟨4 * d.source.1.val, by simp [collarSize]; omega⟩,
        ⟨4 * d.source.2.val + 2, by simp [collarSize]⟩)
  | .east =>
      (⟨4 * d.source.1.val + 2, by simp [collarSize]⟩,
        ⟨4 * d.source.2.val + 4, by simp [collarSize]; omega⟩)
  | .south =>
      (⟨4 * d.source.1.val + 4, by simp [collarSize]; omega⟩,
        ⟨4 * d.source.2.val + 2, by simp [collarSize]⟩)
  | .west =>
      (⟨4 * d.source.1.val + 2, by simp [collarSize]⟩,
        ⟨4 * d.source.2.val, by simp [collarSize]; omega⟩)

/-- First half of a clockwise slot turn. -/
theorem slotPoint_adj_turnCorner {m n : Nat} (v : GridVertex m n)
    (d : GridDirection) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (slotPoint (v, d)) (turnCorner v d) := by
  cases d
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inr rfl⟩
  · exact Or.inr ⟨rfl, Or.inr rfl⟩

/-- Second half of a clockwise slot turn. -/
theorem turnCorner_adj_clockwise_slotPoint {m n : Nat}
    (v : GridVertex m n) (d : GridDirection) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (turnCorner v d) (slotPoint (v, d.clockwise)) := by
  cases d
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inr rfl⟩
  · exact Or.inr ⟨rfl, Or.inr rfl⟩

theorem turnCorner_adj_edgeCorridorCenter {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} (d : GridDirectionalDart T) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (turnCorner d.source d.direction) (edgeCorridorCenter d) := by
  cases hd : d.direction
  · refine Or.inr ⟨?_, Or.inr ?_⟩
    · apply Fin.ext; simp [turnCorner, edgeCorridorCenter, hd]
    · simp [turnCorner, edgeCorridorCenter, hd]
  · refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext; simp [turnCorner, edgeCorridorCenter, hd]
    · simp [turnCorner, edgeCorridorCenter, hd]
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · apply Fin.ext; simp [turnCorner, edgeCorridorCenter, hd]
    · simp [turnCorner, edgeCorridorCenter, hd]
  · refine Or.inl ⟨?_, Or.inr ?_⟩
    · apply Fin.ext; simp [turnCorner, edgeCorridorCenter, hd]
    · simp [turnCorner, edgeCorridorCenter, hd]

theorem edgeCorridorCenter_adj_reverseTurnCorner {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} (d : GridDirectionalDart T) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (edgeCorridorCenter d) (turnCorner d.target d.direction.opposite) := by
  have hstep := d.step
  cases hd : d.direction <;> simp [gridNeighbor?, hd] at hstep
  · rcases hstep with ⟨_, ht⟩
    have hr := congrArg (fun v : GridVertex m n => v.1.val) ht
    have hc := congrArg (fun v : GridVertex m n => v.2.val) ht
    simp at hr hc
    refine Or.inr ⟨?_, Or.inr ?_⟩
    · apply Fin.ext
      simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
    · simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
  · rcases hstep with ⟨_, ht⟩
    have hr := congrArg (fun v : GridVertex m n => v.1.val) ht
    have hc := congrArg (fun v : GridVertex m n => v.2.val) ht
    simp at hr hc
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
    · simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
  · rcases hstep with ⟨_, ht⟩
    have hr := congrArg (fun v : GridVertex m n => v.1.val) ht
    have hc := congrArg (fun v : GridVertex m n => v.2.val) ht
    simp at hr hc
    refine Or.inr ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
    · simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
  · rcases hstep with ⟨_, ht⟩
    have hr := congrArg (fun v : GridVertex m n => v.1.val) ht
    have hc := congrArg (fun v : GridVertex m n => v.2.val) ht
    simp at hr hc
    refine Or.inl ⟨?_, Or.inr ?_⟩
    · apply Fin.ext
      simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega
    · simp [edgeCorridorCenter, turnCorner, hd, GridDirection.opposite]
      omega

/-- A four-edge chord through the centerline corridor of a retained tree edge.
It joins the two expanded slots representing opposite dart orientations. -/
def edgeCorridorChord {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    (d : GridDirectionalDart T) :
    (gridGraph (collarSize m) (collarSize n)).Walk
      (slotPoint (GridExpandedContour.slotOfDart d))
      (slotPoint (GridExpandedContour.slotOfDart d.reverse)) := by
  let p := Walk.cons (slotPoint_adj_turnCorner d.source d.direction)
    (Walk.cons (turnCorner_adj_edgeCorridorCenter d)
      (Walk.cons (edgeCorridorCenter_adj_reverseTurnCorner d)
        (Walk.cons (slotPoint_adj_turnCorner d.target d.direction.opposite).symm
          Walk.nil)))
  exact p.copy rfl rfl

@[simp] theorem length_edgeCorridorChord {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} (d : GridDirectionalDart T) :
    (edgeCorridorChord d).length = 4 := by
  rfl

theorem support_edgeCorridorChord {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} (d : GridDirectionalDart T) :
    (edgeCorridorChord d).support =
      [slotPoint (GridExpandedContour.slotOfDart d),
        turnCorner d.source d.direction,
        edgeCorridorCenter d,
        turnCorner d.target d.direction.opposite,
        slotPoint (GridExpandedContour.slotOfDart d.reverse)] := by
  simp [edgeCorridorChord, GridExpandedContour.slotOfDart,
    GridDirectionalDart.reverse]

theorem edges_edgeCorridorChord {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} (d : GridDirectionalDart T) :
    (edgeCorridorChord d).edges =
      [s(slotPoint (GridExpandedContour.slotOfDart d),
          turnCorner d.source d.direction),
        s(turnCorner d.source d.direction, edgeCorridorCenter d),
        s(edgeCorridorCenter d, turnCorner d.target d.direction.opposite),
        s(turnCorner d.target d.direction.opposite,
          slotPoint (GridExpandedContour.slotOfDart d.reverse))] := by
  simp [edgeCorridorChord, GridExpandedContour.slotOfDart,
    GridDirectionalDart.reverse]

/-- Midpoint of the offset side followed while crossing an occupied edge. -/
def crossingMidpoint {m n : Nat} (v : GridVertex m n) (d : GridDirection) :
    GridVertex (collarSize m) (collarSize n) :=
  match d with
  | .north =>
      (⟨4 * v.1.val, by simp [collarSize]; omega⟩,
        ⟨4 * v.2.val + 1, by simp [collarSize]; omega⟩)
  | .east =>
      (⟨4 * v.1.val + 1, by simp [collarSize]; omega⟩,
        ⟨4 * v.2.val + 4, by simp [collarSize]; omega⟩)
  | .south =>
      (⟨4 * v.1.val + 4, by simp [collarSize]; omega⟩,
        ⟨4 * v.2.val + 3, by simp [collarSize]⟩)
  | .west =>
      (⟨4 * v.1.val + 3, by simp [collarSize]⟩,
        ⟨4 * v.2.val, by simp [collarSize]; omega⟩)

theorem slotPoint_adj_crossingMidpoint {m n : Nat} (v : GridVertex m n)
    (d : GridDirection) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (slotPoint (v, d)) (crossingMidpoint v d) := by
  cases d
  · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inr rfl⟩

theorem crossingMidpoint_adj_successorSlot_of_step {m n : Nat}
    {v w : GridVertex m n} {d : GridDirection}
    (h : gridNeighbor? v d = some w) :
    (gridGraph (collarSize m) (collarSize n)).Adj
      (crossingMidpoint v d) (slotPoint (w, d.opposite.clockwise)) := by
  cases d <;> simp [gridNeighbor?] at h
  all_goals rcases h with ⟨hv, rfl⟩
  · exact Or.inr ⟨rfl, Or.inr (by
      simp [crossingMidpoint, slotPoint, GridDirection.opposite,
        GridDirection.clockwise]
      omega)⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact Or.inl ⟨rfl, Or.inr (by
      simp [crossingMidpoint, slotPoint, GridDirection.opposite,
        GridDirection.clockwise]
      omega)⟩

/-- Two-edge clockwise turn around one original vertex. -/
def turnSegment {m n : Nat} (v : GridVertex m n) (d : GridDirection) :
    (gridGraph (collarSize m) (collarSize n)).Walk
      (slotPoint (v, d)) (slotPoint (v, d.clockwise)) :=
  Walk.cons (slotPoint_adj_turnCorner v d)
    (Walk.cons (turnCorner_adj_clockwise_slotPoint v d) Walk.nil)

@[simp] theorem length_turnSegment {m n : Nat} (v : GridVertex m n)
    (d : GridDirection) : (turnSegment v d).length = 2 := by
  simp [turnSegment]

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Collar realization of one expanded successor.  An occupied step follows
one offset side of its retained edge; an unoccupied step turns clockwise around
its current vertex. -/
def successorSegment (s : GridCompassSlot m n) :
    (gridGraph (collarSize m) (collarSize n)).Walk
      (slotPoint s) (slotPoint (succ (T := T) s)) := by
  by_cases hs : Occupied (T := T) s
  · let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs
    let p := Walk.cons (slotPoint_adj_crossingMidpoint d.source d.direction)
      (Walk.cons (crossingMidpoint_adj_successorSlot_of_step d.step) Walk.nil)
    have hend : slotPoint (d.target, d.direction.opposite.clockwise) =
        slotPoint (succ (T := T) s) := by
      rw [succ_of_occupied hs]
      rfl
    exact p.copy rfl hend
  · let p := turnSegment s.1 s.2
    have hend : slotPoint (s.1, s.2.clockwise) =
        slotPoint (succ (T := T) s) := by
      rw [succ_of_not_occupied hs]
    exact p.copy rfl hend

/-- Unique interior vertex of a local successor segment. -/
def segmentMidpoint (s : GridCompassSlot m n) :
    GridVertex (collarSize m) (collarSize n) :=
  if Occupied (T := T) s then crossingMidpoint s.1 s.2
  else turnCorner s.1 s.2

/-- Exact three-vertex support of every local collar segment. -/
theorem support_successorSegment (s : GridCompassSlot m n) :
    (successorSegment (T := T) s).support =
      [slotPoint s, segmentMidpoint (T := T) s,
        slotPoint (succ (T := T) s)] := by
  by_cases hs : Occupied (T := T) s
  · simp only [successorSegment, dif_pos hs]
    exact (Walk.support_copy _ _ _).trans (by
      simp [Walk.support_cons, segmentMidpoint, hs, succ_of_occupied hs]
      exact ⟨rfl, rfl, rfl⟩)
  · simp only [successorSegment, dif_neg hs, Walk.support_copy,
      turnSegment, Walk.support_cons, Walk.support_nil, segmentMidpoint, if_neg hs]
    rw [succ_of_not_occupied hs]

/-- A local segment midpoint is never an expanded-slot sector point.  Their
coordinate residue classes modulo four are disjoint. -/
theorem segmentMidpoint_ne_slotPoint (s t : GridCompassSlot m n) :
    segmentMidpoint (T := T) s ≠ slotPoint t := by
  rintro h
  rcases s with ⟨v, d⟩
  rcases t with ⟨w, e⟩
  by_cases hs : Occupied (T := T) (v, d)
  all_goals
    fin_cases d <;> fin_cases e
    all_goals
      have hr := congrArg (fun x => x.1.val) h
      have hc := congrArg (fun x => x.2.val) h
      simp [segmentMidpoint, hs, crossingMidpoint, turnCorner, slotPoint] at hr hc
      omega

/-- Equal local segment midpoints force equal source slots.  There are no
corner/crossing exceptions because all eight midpoint kinds have distinct
coordinate residues modulo four. -/
theorem segmentMidpoint_injective :
    Function.Injective (segmentMidpoint (T := T)) := by
  rintro ⟨v, d⟩ ⟨w, e⟩ h
  by_cases hv : Occupied (T := T) (v, d) <;>
    by_cases hw : Occupied (T := T) (w, e)
  all_goals
    fin_cases d <;> fin_cases e
    all_goals
      have hr := congrArg (fun x => x.1.val) h
      have hc := congrArg (fun x => x.2.val) h
      simp [segmentMidpoint, hv, hw, crossingMidpoint, turnCorner] at hr hc
      first
      | omega
      | congr 1
        apply Prod.ext <;> apply Fin.ext <;> omega

theorem turnCorner_injective {m n : Nat} :
    Function.Injective (fun p : GridVertex m n × GridDirection =>
      turnCorner p.1 p.2) := by
  rintro ⟨v, d⟩ ⟨w, e⟩ h
  fin_cases d <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [turnCorner] at hr hc
    first
    | omega
    | congr 1
      apply Prod.ext <;> apply Fin.ext <;> omega

theorem turnCorner_ne_slotPoint {m n : Nat}
    (v : GridVertex m n) (d : GridDirection) (s : GridCompassSlot m n) :
    turnCorner v d ≠ slotPoint s := by
  rcases s with ⟨w, e⟩
  intro h
  fin_cases d <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [turnCorner, slotPoint] at hr hc
    omega

theorem turnCorner_ne_crossingMidpoint {m n : Nat}
    (v : GridVertex m n) (d : GridDirection)
    (w : GridVertex m n) (e : GridDirection) :
    turnCorner v d ≠ crossingMidpoint w e := by
  intro h
  fin_cases d <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [turnCorner, crossingMidpoint] at hr hc
    omega

omit [DecidableRel T.Adj] in
theorem edgeCorridorCenter_ne_slotPoint
    (d : GridDirectionalDart T) (s : GridCompassSlot m n) :
    edgeCorridorCenter d ≠ slotPoint s := by
  rcases s with ⟨w, e⟩
  intro h
  cases hd : d.direction <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [edgeCorridorCenter, slotPoint, hd] at hr hc
    omega

omit [DecidableRel T.Adj] in
theorem edgeCorridorCenter_ne_turnCorner
    (d : GridDirectionalDart T) (v : GridVertex m n) (e : GridDirection) :
    edgeCorridorCenter d ≠ turnCorner v e := by
  intro h
  cases hd : d.direction <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [edgeCorridorCenter, turnCorner, hd] at hr hc
    omega

omit [DecidableRel T.Adj] in
theorem edgeCorridorCenter_ne_crossingMidpoint
    (d : GridDirectionalDart T) (v : GridVertex m n) (e : GridDirection) :
    edgeCorridorCenter d ≠ crossingMidpoint v e := by
  intro h
  cases hd : d.direction <;> fin_cases e
  all_goals
    have hr := congrArg (fun x => x.1.val) h
    have hc := congrArg (fun x => x.2.val) h
    simp [edgeCorridorCenter, crossingMidpoint, hd] at hr hc
    omega

omit [DecidableRel T.Adj] in
/-- The three interior chord vertices avoid every expanded-contour slot. -/
theorem edgeCorridorChord_interior_ne_slotPoint
    (d : GridDirectionalDart T) {x}
    (hx : x ∈ (edgeCorridorChord d).support)
    (hstart : x ≠ slotPoint (slotOfDart d))
    (hfinish : x ≠ slotPoint (slotOfDart d.reverse))
    (s : GridCompassSlot m n) : x ≠ slotPoint s := by
  rw [support_edgeCorridorChord] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (hstart rfl).elim
  · exact turnCorner_ne_slotPoint _ _ _
  · exact edgeCorridorCenter_ne_slotPoint _ _
  · exact turnCorner_ne_slotPoint _ _ _
  · exact (hfinish rfl).elim

/-- The chord centerline is disjoint from all contour segment midpoints.  At
its two turn-corner vertices, equality could only name the corresponding edge
orientation, which is occupied and therefore uses a crossing midpoint instead. -/
theorem edgeCorridorChord_interior_ne_segmentMidpoint
    (d : GridDirectionalDart T) {x}
    (hx : x ∈ (edgeCorridorChord d).support)
    (hstart : x ≠ slotPoint (slotOfDart d))
    (hfinish : x ≠ slotPoint (slotOfDart d.reverse))
    (s : GridCompassSlot m n) : x ≠ segmentMidpoint (T := T) s := by
  rw [support_edgeCorridorChord] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (hstart rfl).elim
  · by_cases hs : Occupied (T := T) s
    · simpa [segmentMidpoint, hs] using
        turnCorner_ne_crossingMidpoint d.source d.direction s.1 s.2
    · intro h
      have heq := turnCorner_injective (m := m) (n := n)
        (a₁ := (d.source, d.direction)) (a₂ := s)
        (by simpa [segmentMidpoint, hs] using h)
      have hsEq : s = slotOfDart d := by
        simpa [slotOfDart] using heq.symm
      exact hs (hsEq ▸ occupied_slotOfDart d)
  · by_cases hs : Occupied (T := T) s
    · simpa [segmentMidpoint, hs] using
        edgeCorridorCenter_ne_crossingMidpoint d s.1 s.2
    · simpa [segmentMidpoint, hs] using
        edgeCorridorCenter_ne_turnCorner d s.1 s.2
  · by_cases hs : Occupied (T := T) s
    · simpa [segmentMidpoint, hs] using
        turnCorner_ne_crossingMidpoint d.target d.direction.opposite s.1 s.2
    · intro h
      have heq := turnCorner_injective (m := m) (n := n)
        (a₁ := (d.target, d.direction.opposite)) (a₂ := s)
        (by simpa [segmentMidpoint, hs] using h)
      have hsEq : s = slotOfDart d.reverse := by
        simpa [slotOfDart, GridDirectionalDart.reverse] using heq.symm
      exact hs (hsEq ▸ occupied_slotOfDart d.reverse)
  · exact (hfinish rfl).elim

omit [DecidableRel T.Adj] in
theorem slotPoint_dart_ne_reverse (d : GridDirectionalDart T) :
    slotPoint (slotOfDart d) ≠ slotPoint (slotOfDart d.reverse) := by
  intro h
  have hslots := slotPoint_injective h
  have hdarts := slotOfDart_injective hslots
  have hv : d.target = d.source := by
    simpa [GridDirectionalDart.reverse] using
      (congrArg GridDirectionalDart.source hdarts).symm
  exact T.loopless.irrefl d.source (hv ▸ d.adj)

omit [DecidableRel T.Adj] in
theorem edgeCorridorChord_isPath (d : GridDirectionalDart T) :
    (edgeCorridorChord d).IsPath := by
  rw [Walk.isPath_def, support_edgeCorridorChord]
  have hends := slotPoint_dart_ne_reverse (T := T) d
  have hturns : turnCorner d.source d.direction ≠
      turnCorner d.target d.direction.opposite := by
    intro h
    have hp := turnCorner_injective (m := m) (n := n)
      (a₁ := (d.source, d.direction))
      (a₂ := (d.target, d.direction.opposite)) h
    have hd := congrArg Prod.snd hp
    cases hdir : d.direction <;>
      simp [GridDirection.opposite, hdir] at hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, or_false, not_or]
  exact ⟨⟨(turnCorner_ne_slotPoint _ _ _).symm,
      (edgeCorridorCenter_ne_slotPoint d _).symm,
      (turnCorner_ne_slotPoint _ _ _).symm, hends⟩,
    ⟨⟨edgeCorridorCenter_ne_turnCorner d _ _ |>.symm, hturns,
        turnCorner_ne_slotPoint _ _ _⟩,
      ⟨⟨edgeCorridorCenter_ne_turnCorner d _ _,
          edgeCorridorCenter_ne_slotPoint d _⟩,
        ⟨turnCorner_ne_slotPoint _ _ _, ⟨by simp, trivial⟩⟩⟩⟩⟩

/-- Two internally vertex-disjoint, edge-disjoint paths with common distinct
endpoints form a simple cycle. -/
theorem reverse_append_isCycle_of_paths
    {G : SimpleGraph α} {a b : α} [DecidableEq α]
    (p q : G.Walk a b) (hab : a ≠ b)
    (hp : p.IsPath) (hq : q.IsPath)
    (hedges : List.Disjoint p.edges q.edges)
    (hsupport : ∀ {x}, x ∈ p.support → x ∈ q.support → x = a ∨ x = b) :
    (p.reverse.append q).IsCycle := by
  rw [Walk.isCycle_def]
  have hpRev := hp.reverse
  have hedgeNodup : (p.reverse.append q).edges.Nodup := by
    rw [Walk.edges_append, Walk.edges_reverse]
    apply List.Nodup.append
    · simpa only [List.nodup_reverse] using hp.1.1
    · exact hq.1.1
    · simpa [List.disjoint_reverse_left] using hedges
  have hpTail : b ∉ p.reverse.support.tail := by
    have hn := hpRev.support_nodup
    rw [← p.reverse.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have hqTail : a ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [← q.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have htailDisjoint : List.Disjoint p.reverse.support.tail q.support.tail := by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxpSupport : x ∈ p.support := by
      rw [Walk.support_reverse] at hxp
      exact List.mem_reverse.mp (List.mem_of_mem_tail hxp)
    have hxqSupport : x ∈ q.support := List.mem_of_mem_tail hxq
    rcases hsupport hxpSupport hxqSupport with rfl | rfl
    · exact hqTail hxq
    · exact hpTail hxp
  have htailNodup : (p.reverse.append q).support.tail.Nodup := by
    rw [Walk.tail_support_append]
    exact List.Nodup.append hpRev.support_nodup.tail hq.support_nodup.tail
      htailDisjoint
  have hne : p.reverse.append q ≠ Walk.nil := by
    intro hnil
    have hlen := congrArg Walk.length hnil
    have hpzero : p.length = 0 := by
      simp only [Walk.length_append, Walk.length_reverse, Walk.length_nil] at hlen
      omega
    exact hab (Walk.exists_length_eq_zero_iff.mp ⟨p, hpzero⟩)
  exact ⟨⟨hedgeNodup⟩, hne, htailNodup⟩

theorem succ_ne (s : GridCompassSlot m n) : succ (T := T) s ≠ s := by
  intro h
  by_cases hs : Occupied (T := T) s
  · let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs
    have hv : d.target = d.source := by
      change d.target = s.1
      simpa only [succ_of_occupied hs] using congrArg Prod.fst h
    exact T.loopless.irrefl d.source (hv ▸ d.adj)
  · have hd : s.2.clockwise = s.2 := by
      simpa [succ_of_not_occupied hs] using congrArg Prod.snd h
    exact GridDirection.clockwise_ne_self s.2 hd

/-- The two undirected half-edges of one collar successor segment. -/
def localEdge (s : GridCompassSlot m n) (second : Bool) :
    Sym2 (GridVertex (collarSize m) (collarSize n)) :=
  if second then s(segmentMidpoint (T := T) s, slotPoint (succ (T := T) s))
  else s(slotPoint s, segmentMidpoint (T := T) s)

/-- A collar half-edge determines both its expanded source slot and which half
of the local segment it is.  In particular the first and final reverse-edge
collision cannot occur. -/
theorem localEdge_injective :
    Function.Injective (fun p : GridCompassSlot m n × Bool =>
      localEdge (T := T) p.1 p.2) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  cases a <;> cases b <;> simp only [localEdge, Bool.false_eq_true,
    if_false, if_true] at h
  all_goals rw [Sym2.eq_iff] at h
  · rcases h with h | h
    · exact Prod.ext (slotPoint_injective h.1) rfl
    · exact (segmentMidpoint_ne_slotPoint (T := T) t s h.1.symm).elim
  · rcases h with h | h
    · exact (segmentMidpoint_ne_slotPoint (T := T) t s h.1.symm).elim
    · have hst := segmentMidpoint_injective (T := T) h.2
      subst t
      exact (succ_ne (T := T) s (slotPoint_injective h.1).symm).elim
  · rcases h with h | h
    · exact (segmentMidpoint_ne_slotPoint (T := T) s t h.1).elim
    · have hst := segmentMidpoint_injective (T := T) h.1
      subst t
      exact (succ_ne (T := T) s (slotPoint_injective h.2)).elim
  · rcases h with h | h
    · exact Prod.ext (segmentMidpoint_injective (T := T) h.1) rfl
    · exact (segmentMidpoint_ne_slotPoint (T := T) s
        (succ (T := T) t) h.1).elim

/-- Exact edge list of one local segment. -/
theorem edges_successorSegment (s : GridCompassSlot m n) :
    (successorSegment (T := T) s).edges =
      [localEdge (T := T) s false, localEdge (T := T) s true] := by
  by_cases hs : Occupied (T := T) s
  · simp only [successorSegment, dif_pos hs]
    exact (Walk.edges_copy _ _ _).trans (by
      simp [Walk.edges_cons, localEdge, segmentMidpoint, hs, succ_of_occupied hs]
      exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩)
  · simp only [successorSegment, dif_neg hs, Walk.edges_copy,
      turnSegment, Walk.edges_cons, Walk.edges_nil]
    simp [localEdge, segmentMidpoint, hs, succ_of_not_occupied hs]

/-- Occupied successors pass through the midpoint of one offset side of their
retained edge. -/
theorem crossingMidpoint_mem_successorSegment_of_occupied
    {s : GridCompassSlot m n} (hs : Occupied (T := T) s) :
    crossingMidpoint s.1 s.2 ∈ (successorSegment (T := T) s).support := by
  simp [support_successorSegment, segmentMidpoint, hs]

/-- Unoccupied successors pass through the local clockwise turn corner. -/
theorem turnCorner_mem_successorSegment_of_not_occupied
    {s : GridCompassSlot m n} (hs : ¬Occupied (T := T) s) :
    turnCorner s.1 s.2 ∈ (successorSegment (T := T) s).support := by
  simp [support_successorSegment, segmentMidpoint, hs]

@[simp] theorem length_successorSegment (s : GridCompassSlot m n) :
    (successorSegment (T := T) s).length = 2 := by
  unfold successorSegment
  split <;> exact (Walk.length_copy _ _ _).trans rfl

/-- Every local segment ends where the next local segment begins. -/
theorem successorSegment_endpoint_continuity (s : GridCompassSlot m n) :
    (successorSegment (T := T) s).support.getLast (by simp) =
      (successorSegment (T := T) (succ (T := T) s)).support.head
        (by simp) := by
  simp

/-- Explicit alternating support list for a finite collar trace. -/
def collarVertexList (s : GridCompassSlot m n) : Nat →
    List (GridVertex (collarSize m) (collarSize n))
  | 0 => [slotPoint s]
  | k + 1 => slotPoint s :: segmentMidpoint (T := T) s ::
      collarVertexList (succ (T := T) s) k

/-- Edge labels of a finite collar interval. -/
def collarEdgeList (s : GridCompassSlot m n) : Nat →
    List (Sym2 (GridVertex (collarSize m) (collarSize n)))
  | 0 => []
  | k + 1 => localEdge (T := T) s false :: localEdge (T := T) s true ::
      collarEdgeList (succ (T := T) s) k

/-- Finite continuous collar realization of an expanded-contour interval. -/
def collarTrace (s : GridCompassSlot m n) :
    (k : Nat) → (gridGraph (collarSize m) (collarSize n)).Walk
      (slotPoint s) (slotPoint (advance (T := T) s k))
  | 0 => Walk.nil
  | k + 1 =>
      (successorSegment (T := T) s).append
        (collarTrace (succ (T := T) s) k)

/-- Exact vertex support of a finite collar trace. -/
theorem support_collarTrace (s : GridCompassSlot m n) (k : Nat) :
    (collarTrace (T := T) s k).support = collarVertexList (T := T) s k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change ((successorSegment (T := T) s).append
        (collarTrace (T := T) (succ (T := T) s) k)).support = _
      rw [Walk.support_append_eq_support_dropLast_append,
        support_successorSegment, ih]
      rfl

theorem edges_collarTrace (s : GridCompassSlot m n) (k : Nat) :
    (collarTrace (T := T) s k).edges = collarEdgeList (T := T) s k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change ((successorSegment (T := T) s).append
        (collarTrace (T := T) (succ (T := T) s) k)).edges = _
      rw [Walk.edges_append, edges_successorSegment, ih]
      rfl

theorem collarEdgeList_add (s : GridCompassSlot m n) (a b : Nat) :
    collarEdgeList (T := T) s (a + b) =
      collarEdgeList (T := T) s a ++
        collarEdgeList (T := T) (advance (T := T) s a) b := by
  induction a generalizing s with
  | zero => simp [collarEdgeList, advance]
  | succ a ih =>
      simp only [Nat.succ_add, collarEdgeList, List.cons_append]
      rw [ih]
      rfl

theorem mem_collarEdgeList_iff (s : GridCompassSlot m n) (k : Nat)
    (e : Sym2 (GridVertex (collarSize m) (collarSize n))) :
    e ∈ collarEdgeList (T := T) s k ↔
      ∃ i < k, ∃ b : Bool,
        e = localEdge (T := T) (advance (T := T) s i) b := by
  induction k generalizing s e with
  | zero => simp [collarEdgeList]
  | succ k ih =>
      simp only [collarEdgeList, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | ⟨i, hi, b, rfl⟩)
        · exact ⟨0, by omega, false, rfl⟩
        · exact ⟨0, by omega, true, rfl⟩
        · exact ⟨i + 1, by omega, b, rfl⟩
      · rintro ⟨i, hi, b, rfl⟩
        cases i with
        | zero =>
            cases b
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
        | succ i => exact Or.inr (Or.inr ⟨i, by omega, b, rfl⟩)

/-- Source-slot nonrepetition makes the complete collar edge list a trail;
`localEdge_injective` handles the possible reversed first/final edge. -/
theorem nodup_collarEdgeList_of_advance_injective
    (s : GridCompassSlot m n) (k : Nat)
    (hslots : ∀ i j, i < k → j < k →
      advance (T := T) s i = advance (T := T) s j → i = j) :
    (collarEdgeList (T := T) s k).Nodup := by
  induction k generalizing s with
  | zero => simp [collarEdgeList]
  | succ k ih =>
      rw [collarEdgeList, List.nodup_cons, List.mem_cons,
        List.nodup_cons]
      have hshift : ∀ i j, i < k → j < k →
          advance (T := T) (succ (T := T) s) i =
            advance (T := T) (succ (T := T) s) j → i = j := by
        intro i j hi hj hij
        have := hslots (i + 1) (j + 1) (by omega) (by omega) hij
        omega
      refine ⟨?_, ?_, ih (succ (T := T) s) hshift⟩
      · intro h
        rcases h with heq | hmem
        · exact Bool.noConfusion
            (congrArg Prod.snd (localEdge_injective (T := T)
              (a₁ := (s, false)) (a₂ := (s, true)) heq))
        · rcases (mem_collarEdgeList_iff (T := T)
            (succ (T := T) s) k _).1 hmem with ⟨i, hi, b, heq⟩
          have hp := localEdge_injective (T := T) (a₁ := (s, false))
            (a₂ := (advance (T := T) (succ (T := T) s) i, b)) heq
          have hz := hslots 0 (i + 1) (by omega) (by omega)
            (congrArg Prod.fst hp)
          omega
      · intro hmem
        rcases (mem_collarEdgeList_iff (T := T)
            (succ (T := T) s) k _).1 hmem with ⟨i, hi, b, heq⟩
        have hp := localEdge_injective (T := T) (a₁ := (s, true))
          (a₂ := (advance (T := T) (succ (T := T) s) i, b)) heq
        have hz := hslots 0 (i + 1) (by omega) (by omega)
          (congrArg Prod.fst hp)
        omega

/-- Membership in a collar support list is either a slot sector at an index no
later than the endpoint or a segment midpoint at a strictly earlier index. -/
theorem mem_collarVertexList_iff (s : GridCompassSlot m n) (k : Nat)
    (x : GridVertex (collarSize m) (collarSize n)) :
    x ∈ collarVertexList (T := T) s k ↔
      (∃ i ≤ k, x = slotPoint (advance (T := T) s i)) ∨
      (∃ i < k, x = segmentMidpoint (T := T) (advance (T := T) s i)) := by
  induction k generalizing s x with
  | zero => simp [collarVertexList, advance]
  | succ k ih =>
      simp only [collarVertexList, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | h)
        · exact Or.inl ⟨0, by omega, rfl⟩
        · exact Or.inr ⟨0, by omega, rfl⟩
        · rcases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
          · exact Or.inl ⟨i + 1, by omega, by rfl⟩
          · exact Or.inr ⟨i + 1, by omega, by rfl⟩
      · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
        · cases i with
          | zero => exact Or.inl rfl
          | succ i =>
              exact Or.inr (Or.inr (Or.inl ⟨i, by omega, rfl⟩))
        · cases i with
          | zero => exact Or.inr (Or.inl rfl)
          | succ i =>
              exact Or.inr (Or.inr (Or.inr ⟨i, by omega, rfl⟩))

/-- Every chord interior vertex avoids every finite expanded-contour trace. -/
theorem edgeCorridorChord_interior_not_mem_collarTrace
    (d : GridDirectionalDart T) {x}
    (hx : x ∈ (edgeCorridorChord d).support)
    (hstart : x ≠ slotPoint (slotOfDart d))
    (hfinish : x ≠ slotPoint (slotOfDart d.reverse))
    (s : GridCompassSlot m n) (k : Nat) :
    x ∉ (collarTrace (T := T) s k).support := by
  rw [support_collarTrace]
  intro hmem
  rcases (mem_collarVertexList_iff (T := T) s k x).1 hmem with
    ⟨i, _, hi⟩ | ⟨i, _, hi⟩
  · exact edgeCorridorChord_interior_ne_slotPoint d hx hstart hfinish _ hi
  · exact edgeCorridorChord_interior_ne_segmentMidpoint d hx hstart hfinish _ hi

/-- Nonrepetition of the expanded slots through the endpoint implies
nonrepetition of every vertex in the realized collar interval. -/
theorem nodup_collarVertexList_of_advance_injective
    (s : GridCompassSlot m n) (k : Nat)
    (hslots : ∀ i j, i ≤ k → j ≤ k →
      advance (T := T) s i = advance (T := T) s j → i = j) :
    (collarVertexList (T := T) s k).Nodup := by
  induction k generalizing s with
  | zero => simp [collarVertexList]
  | succ k ih =>
      rw [collarVertexList, List.nodup_cons, List.mem_cons,
        List.nodup_cons]
      have hshift : ∀ i j, i ≤ k → j ≤ k →
          advance (T := T) (succ (T := T) s) i =
            advance (T := T) (succ (T := T) s) j → i = j := by
        intro i j hi hj hij
        have := hslots (i + 1) (j + 1) (by omega) (by omega) hij
        omega
      refine ⟨?_, ?_, ih (succ (T := T) s) hshift⟩
      · intro h
        rcases h with heq | hmem
        · exact segmentMidpoint_ne_slotPoint (T := T) s s heq.symm
        ·
          rcases (mem_collarVertexList_iff (T := T)
              (succ (T := T) s) k (slotPoint s)).1 hmem with
            ⟨i, hi, heq⟩ | ⟨i, hi, heq⟩
          · have hslot := slotPoint_injective heq
            have hz := hslots 0 (i + 1) (by omega) (by omega) hslot
            omega
          · exact segmentMidpoint_ne_slotPoint (T := T)
              (advance (T := T) (succ (T := T) s) i) s heq.symm
      · intro hmem
        rcases (mem_collarVertexList_iff (T := T)
            (succ (T := T) s) k (segmentMidpoint (T := T) s)).1 hmem with
          ⟨i, hi, heq⟩ | ⟨i, hi, heq⟩
        · exact segmentMidpoint_ne_slotPoint (T := T) s _ heq
        · have hslot := segmentMidpoint_injective (T := T) heq
          have hz := hslots 0 (i + 1) (by omega) (by omega) hslot
          omega

/-- A nonrepeating expanded-slot interval realizes as a simple collar path. -/
theorem collarTrace_isPath_of_advance_injective
    (s : GridCompassSlot m n) (k : Nat)
    (hslots : ∀ i j, i ≤ k → j ≤ k →
      advance (T := T) s i = advance (T := T) s j → i = j) :
    (collarTrace (T := T) s k).IsPath := by
  rw [Walk.isPath_def, support_collarTrace]
  exact nodup_collarVertexList_of_advance_injective s k hslots

/-- Close a collar trace whose expanded-slot endpoint returns to its start. -/
def orbitCollarWalk (s : GridCompassSlot m n) (k : Nat)
    (hperiod : advance (T := T) s k = s) :
    (gridGraph (collarSize m) (collarSize n)).Walk (slotPoint s) (slotPoint s) :=
  (collarTrace (T := T) s k).copy rfl (congrArg slotPoint hperiod)

/-- A nontrivial first-return expanded orbit realizes as a simple collar
cycle.  Edge nonrepetition follows from injective `(slot, half)` labels. -/
theorem orbitCollarWalk_isCycle
    (s : GridCompassSlot m n) (k : Nat) (hk : 0 < k)
    (hperiod : advance (T := T) s k = s)
    (hslots : ∀ i j, i < k → j < k →
      advance (T := T) s i = advance (T := T) s j → i = j) :
    (orbitCollarWalk (T := T) s k hperiod).IsCycle := by
  rw [Walk.isCycle_def]
  have hedge : (orbitCollarWalk (T := T) s k hperiod).edges.Nodup := by
    rw [orbitCollarWalk, Walk.edges_copy, edges_collarTrace]
    exact nodup_collarEdgeList_of_advance_injective s k hslots
  have hne : orbitCollarWalk (T := T) s k hperiod ≠ Walk.nil := by
    intro hnil
    have he := congrArg Walk.edges hnil
    rw [orbitCollarWalk, Walk.edges_copy, edges_collarTrace] at he
    cases k with
    | zero => omega
    | succ q => simp [collarEdgeList] at he
  refine ⟨⟨hedge⟩, hne, ?_⟩
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [orbitCollarWalk, Walk.support_copy, support_collarTrace,
    collarVertexList, List.tail_cons, List.nodup_cons]
  have hclosedUnique : ∀ a b, 0 < a → a ≤ q + 1 → 0 < b → b ≤ q + 1 →
      advance (T := T) s a = advance (T := T) s b → a = b := by
    intro a b ha ha' hb hb' hab
    by_cases haLast : a = q + 1
    · by_cases hbLast : b = q + 1
      · omega
      · have hbLt : b < q + 1 := by omega
        have h0b : advance (T := T) s 0 = advance (T := T) s b := by
          change s = advance (T := T) s b
          simpa [haLast, hperiod] using hab
        have := hslots 0 b (by omega) hbLt h0b
        omega
    · by_cases hbLast : b = q + 1
      · have haLt : a < q + 1 := by omega
        have ha0 : advance (T := T) s a = advance (T := T) s 0 := by
          change advance (T := T) s a = s
          simpa [hbLast, hperiod] using hab
        have := hslots a 0 haLt (by omega) ha0
        omega
      · exact hslots a b (by omega) (by omega) hab
  have hshift : ∀ i j, i ≤ q → j ≤ q →
      advance (T := T) (succ (T := T) s) i =
        advance (T := T) (succ (T := T) s) j → i = j := by
    intro i j hi hj hij
    have := hclosedUnique (i + 1) (j + 1) (by omega) (by omega)
      (by omega) (by omega) hij
    omega
  refine ⟨?_, nodup_collarVertexList_of_advance_injective
    (succ (T := T) s) q hshift⟩
  intro hmem
  rcases (mem_collarVertexList_iff (T := T) (succ (T := T) s) q
      (segmentMidpoint (T := T) s)).1 hmem with
    ⟨i, hi, heq⟩ | ⟨i, hi, heq⟩
  · exact segmentMidpoint_ne_slotPoint (T := T) s _ heq
  · have hsEq := segmentMidpoint_injective (T := T) heq
    have hz := hslots 0 (i + 1) (by omega) (by omega) hsEq
    omega

/-- Collar cycle obtained by following a nonfixed point for the order of a
cyclic expanded permutation. -/
def orderCollarWalk (_hcycle : Equiv.Perm.IsCycle (equiv (T := T)))
    (s : GridCompassSlot m n) (_hs : equiv (T := T) s ≠ s) :
    (gridGraph (collarSize m) (collarSize n)).Walk (slotPoint s) (slotPoint s) :=
  orbitCollarWalk (T := T) s (orderOf (equiv (T := T))) (by
    rw [advance_eq_iterate]
    change ((equiv (T := T) ^ orderOf (equiv (T := T))) s) = s
    rw [pow_orderOf_eq_one]
    rfl)

theorem orderCollarWalk_isCycle
    (hcycle : Equiv.Perm.IsCycle (equiv (T := T)))
    (s : GridCompassSlot m n) (hs : equiv (T := T) s ≠ s) :
    (orderCollarWalk (T := T) hcycle s hs).IsCycle := by
  unfold orderCollarWalk
  apply orbitCollarWalk_isCycle
  · rw [hcycle.orderOf]
    exact lt_of_lt_of_le Nat.zero_lt_two hcycle.two_le_card_support
  · intro i j hi hj hij
    have hp : equiv (T := T) ^ i = equiv (T := T) ^ j :=
      hcycle.pow_eq_pow_iff.mpr ⟨s, hs, by
        simpa only [advance_eq_iterate, Equiv.Perm.coe_pow] using hij⟩
    exact pow_injOn_Iio_orderOf hi hj hp

/-- The full offset-collar cycle of a square-grid spanning tree, based at any
expanded slot. -/
def spanningTreeCollarCycle {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (s : GridCompassSlot n n) :
    (gridGraph (collarSize n) (collarSize n)).Walk (slotPoint s) (slotPoint s) :=
  orderCollarWalk (T := T) (equiv_isCycle_of_spanningSquareTree hn hT) s (by
    simpa only [equiv_apply] using succ_ne (T := T) s)

theorem spanningTreeCollarCycle_isCycle {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (s : GridCompassSlot n n) :
    (spanningTreeCollarCycle hn hT s).IsCycle :=
  orderCollarWalk_isCycle (equiv_isCycle_of_spanningSquareTree hn hT) s
    (by simpa only [equiv_apply] using succ_ne (T := T) s)

/-- Bounded-side face carrier cut out by the global expanded-contour collar
cycle. -/
def spanningTreeCollarInteriorFaces {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (s : GridCompassSlot n n) : Finset (GridFace (collarSize n) (collarSize n)) :=
  cycleInteriorFaces (spanningTreeCollarCycle hn hT s)

@[simp] theorem out_not_mem_spanningTreeCollarInteriorFaces {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (s : GridCompassSlot n n) :
    GridFace.out ∉ spanningTreeCollarInteriorFaces hn hT s :=
  out_not_mem_cycleInteriorFaces _

@[simp] theorem length_collarTrace (s : GridCompassSlot m n) (k : Nat) :
    (collarTrace (T := T) s k).length = 2 * k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change ((successorSegment (T := T) s).append
        (collarTrace (T := T) (succ (T := T) s) k)).length = _
      rw [Walk.length_append, length_successorSegment, ih]
      omega

/-- Standard-iterate endpoint form of the finite collar trace. -/
def iterateCollarTrace (s : GridCompassSlot m n) (k : Nat) :
    (gridGraph (collarSize m) (collarSize n)).Walk
      (slotPoint s) (slotPoint ((equiv (T := T)^[k]) s)) :=
  (collarTrace (T := T) s k).copy rfl
    (congrArg slotPoint (advance_eq_iterate s k))

theorem edges_iterateCollarTrace (s : GridCompassSlot m n) (k : Nat) :
    (iterateCollarTrace (T := T) s k).edges = collarEdgeList (T := T) s k := by
  rw [iterateCollarTrace, Walk.edges_copy, edges_collarTrace]

@[simp] theorem length_iterateCollarTrace (s : GridCompassSlot m n) (k : Nat) :
    (iterateCollarTrace (T := T) s k).length = 2 * k := by
  simp [iterateCollarTrace]

end

end GridExpandedContour

end GridGraphs
