import GridGraphs.Geometry.GridEdge

/-!
# Compass directions and oriented tree edges

The contour of an embedded grid tree follows directed tree edges and, at each
vertex, takes the next incident tree edge in cyclic compass order.  This module
provides the finite coordinate data for that rotation.
-/

namespace GridGraphs

/-- Clockwise compass directions in grid coordinates. -/
inductive GridDirection where
  | north | east | south | west
  deriving DecidableEq, Repr

namespace GridDirection

instance : Fintype GridDirection :=
  ⟨{north, east, south, west}, by intro x; cases x <;> simp⟩

/-- One clockwise quarter-turn. -/
def clockwise : GridDirection → GridDirection
  | north => east
  | east => south
  | south => west
  | west => north

/-- The reverse compass direction. -/
def opposite : GridDirection → GridDirection
  | north => south
  | east => west
  | south => north
  | west => east

@[simp] theorem opposite_opposite (d : GridDirection) :
    d.opposite.opposite = d := by cases d <;> rfl

@[simp] theorem clockwise_four (d : GridDirection) :
    d.clockwise.clockwise.clockwise.clockwise = d := by cases d <;> rfl

@[simp] theorem clockwise_ne_self (d : GridDirection) : d.clockwise ≠ d := by
  cases d <;> decide

/-- The next member of `S` encountered strictly clockwise from `d`, returning
to `d` only when no other direction in the cycle belongs to `S`. -/
def nextIn (S : Finset GridDirection) (d : GridDirection) : GridDirection :=
  if d.clockwise ∈ S then d.clockwise
  else if d.clockwise.clockwise ∈ S then d.clockwise.clockwise
  else if d.clockwise.clockwise.clockwise ∈ S then d.clockwise.clockwise.clockwise
  else d

theorem nextIn_mem {S : Finset GridDirection} {d : GridDirection}
    (hd : d ∈ S) : d.nextIn S ∈ S := by
  unfold nextIn
  split <;> rename_i h₁
  · exact h₁
  · split <;> rename_i h₂
    · exact h₂
    · split <;> rename_i h₃
      · exact h₃
      · exact hd

/-- On a set of occupied directions, clockwise successor is injective. -/
theorem nextIn_injective_on (S : Finset GridDirection) :
    Set.InjOn (nextIn S) (↑S : Set GridDirection) := by
  intro a ha b hb hab
  fin_cases a <;> fin_cases b <;>
    by_cases hn : GridDirection.north ∈ S <;>
    by_cases he : GridDirection.east ∈ S <;>
    by_cases hs : GridDirection.south ∈ S <;>
    by_cases hw : GridDirection.west ∈ S <;>
    simp_all [nextIn, clockwise]

/-- At most three clockwise successor steps connect any two occupied compass
directions. -/
theorem mem_eq_or_eq_nextIn_or_eq_nextIn_two_or_eq_nextIn_three
    (S : Finset GridDirection) {a b : GridDirection}
    (ha : a ∈ S) (hb : b ∈ S) :
    b = a ∨ b = a.nextIn S ∨
      b = (a.nextIn S).nextIn S ∨
      b = ((a.nextIn S).nextIn S).nextIn S := by
  fin_cases a <;> fin_cases b <;>
    by_cases hn : GridDirection.north ∈ S <;>
    by_cases he : GridDirection.east ∈ S <;>
    by_cases hs : GridDirection.south ∈ S <;>
    by_cases hw : GridDirection.west ∈ S <;>
    simp_all [nextIn, clockwise]

end GridDirection

/-- Neighbor one step from `v` in direction `d`, when that step stays in the
rectangular grid. -/
def gridNeighbor? {m n : Nat} (v : GridVertex m n) :
    GridDirection → Option (GridVertex m n)
  | .north =>
      if h : 0 < v.1.val then
        some (⟨v.1.val - 1, by omega⟩, v.2)
      else none
  | .east =>
      if h : v.2.val + 1 < n then
        some (v.1, ⟨v.2.val + 1, h⟩)
      else none
  | .south =>
      if h : v.1.val + 1 < m then
        some (⟨v.1.val + 1, h⟩, v.2)
      else none
  | .west =>
      if h : 0 < v.2.val then
        some (v.1, ⟨v.2.val - 1, by omega⟩)
      else none

/-- A successful compass step is a grid edge. -/
theorem gridNeighbor?_adj {m n : Nat} {v w : GridVertex m n}
    {d : GridDirection} (h : gridNeighbor? v d = some w) :
    (gridGraph m n).Adj v w := by
  cases d with
  | north =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      right
      refine ⟨rfl, Or.inr ?_⟩
      change v.1.val - 1 + 1 = v.1.val
      omega
  | east =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      left
      exact ⟨rfl, Or.inl rfl⟩
  | south =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      right
      exact ⟨rfl, Or.inl rfl⟩
  | west =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      left
      refine ⟨rfl, Or.inr ?_⟩
      change v.2.val - 1 + 1 = v.2.val
      omega

/-- Reversing a successful compass step returns to its source. -/
theorem gridNeighbor?_opposite {m n : Nat} {v w : GridVertex m n}
    {d : GridDirection} (h : gridNeighbor? v d = some w) :
    gridNeighbor? w d.opposite = some v := by
  cases d with
  | north =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      simp [GridDirection.opposite, gridNeighbor?, show v.1.val - 1 + 1 < m by omega]
      apply Prod.ext
      · apply Fin.ext
        simp
        omega
      · rfl

  | east =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      simp [GridDirection.opposite, gridNeighbor?]
  | south =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      simp [GridDirection.opposite, gridNeighbor?]
  | west =>
      simp [gridNeighbor?] at h
      rcases h with ⟨hv, rfl⟩
      simp [GridDirection.opposite, gridNeighbor?, show v.2.val - 1 + 1 < n by omega]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp
        omega

/-- A source and target determine the compass direction of a grid step. -/
theorem gridNeighbor?_direction_unique {m n : Nat}
    {v w : GridVertex m n} {d e : GridDirection}
    (hd : gridNeighbor? v d = some w)
    (he : gridNeighbor? v e = some w) : d = e := by
  fin_cases d <;> fin_cases e <;> try rfl
  all_goals
    simp [gridNeighbor?] at hd he
    rcases hd with ⟨_, hd⟩
    rcases he with ⟨_, he⟩
    have hr := congrArg (fun x : GridVertex m n => x.1.val) (hd.trans he.symm)
    have hc := congrArg (fun x : GridVertex m n => x.2.val) (hd.trans he.symm)
    simp at hr hc
    try omega

/-- Canonical direction of a coordinate edge from its first primal endpoint to
its second. -/
def GridEdge.forwardDirection {m n : Nat} : GridEdge m n → GridDirection
  | .horizontal _ => .east
  | .vertical _ => .south

/-- Source endpoint for an orientation flag. -/
def GridEdge.orientedSource {m n : Nat} (e : GridEdge m n) (forward : Bool) :
    GridVertex m n :=
  if forward then e.primalEndpoints.1 else e.primalEndpoints.2

/-- Target endpoint for an orientation flag. -/
def GridEdge.orientedTarget {m n : Nat} (e : GridEdge m n) (forward : Bool) :
    GridVertex m n :=
  if forward then e.primalEndpoints.2 else e.primalEndpoints.1

/-- Direction in which an oriented edge leaves its source. -/
def GridEdge.orientedDirection {m n : Nat} (e : GridEdge m n) (forward : Bool) :
    GridDirection :=
  if forward then e.forwardDirection else e.forwardDirection.opposite

@[simp] theorem GridEdge.orientedSource_not {m n : Nat}
    (e : GridEdge m n) (forward : Bool) :
    e.orientedSource (!forward) = e.orientedTarget forward := by
  cases forward <;> simp [GridEdge.orientedSource, GridEdge.orientedTarget]

@[simp] theorem GridEdge.orientedTarget_not {m n : Nat}
    (e : GridEdge m n) (forward : Bool) :
    e.orientedTarget (!forward) = e.orientedSource forward := by
  cases forward <;> simp [GridEdge.orientedSource, GridEdge.orientedTarget]

@[simp] theorem GridEdge.orientedDirection_not {m n : Nat}
    (e : GridEdge m n) (forward : Bool) :
    e.orientedDirection (!forward) = (e.orientedDirection forward).opposite := by
  cases forward <;> simp [GridEdge.orientedDirection]

/-- An oriented edge belonging to a specified grid subgraph. -/
structure GridSubgraphDart {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) where
  edge : GridEdge m n
  forward : Bool
  adj : T.Adj (edge.orientedSource forward) (edge.orientedTarget forward)

namespace GridSubgraphDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)}

theorem ext {a b : GridSubgraphDart T} (he : a.edge = b.edge)
    (hf : a.forward = b.forward) : a = b := by
  cases a
  cases b
  simp_all

instance : Finite (GridSubgraphDart T) :=
  Finite.of_injective
    (fun d : GridSubgraphDart T => (d.edge, d.forward))
    (by
      intro a b h
      exact ext (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance [DecidableRel T.Adj] : Fintype (GridSubgraphDart T) :=
  Fintype.ofFinite _

instance : DecidableEq (GridSubgraphDart T) := by
  intro a b
  by_cases he : a.edge = b.edge
  · by_cases hf : a.forward = b.forward
    · exact isTrue (ext he hf)
    · exact isFalse (fun h => hf (congrArg GridSubgraphDart.forward h))
  · exact isFalse (fun h => he (congrArg GridSubgraphDart.edge h))

/-- Reverse an oriented subgraph edge. -/
def reverse (d : GridSubgraphDart T) : GridSubgraphDart T where
  edge := d.edge
  forward := !d.forward
  adj := by simpa using d.adj.symm

@[simp] theorem reverse_reverse (d : GridSubgraphDart T) :
    d.reverse.reverse = d := by
  apply ext <;> simp [reverse]

/-- Edge reversal as an involutive equivalence. -/
def reverseEquiv : GridSubgraphDart T ≃ GridSubgraphDart T where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

end GridSubgraphDart

/-- A grid-tree dart represented by its source and compass direction. -/
structure GridDirectionalDart {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) where
  source : GridVertex m n
  direction : GridDirection
  target : GridVertex m n
  step : gridNeighbor? source direction = some target
  adj : T.Adj source target

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)}

/-- Every oriented edge of a grid subgraph has a compass-direction dart. -/
theorem exists_of_adj (hTgrid : T ≤ gridGraph m n)
    {v w : GridVertex m n} (hvw : T.Adj v w) :
    ∃ d : GridDirectionalDart T, d.source = v ∧ d.target = w := by
  rcases gridGraph_adj_exists_coordinate_edge (hTgrid hvw) with h | h
  · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
    · refine ⟨⟨_, .east, _, ?_, hvw⟩, rfl, rfl⟩
      have hcol : e.col.val + 1 < n := by have := e.col.isLt; omega
      simp [gridNeighbor?, horizontalPrimalEndpoints, hcol]
    · refine ⟨⟨_, .west, _, ?_, hvw⟩, rfl, rfl⟩
      simp [gridNeighbor?, horizontalPrimalEndpoints]
  · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
    · refine ⟨⟨_, .south, _, ?_, hvw⟩, rfl, rfl⟩
      have hrow : e.row.val + 1 < m := by have := e.row.isLt; omega
      simp [gridNeighbor?, verticalPrimalEndpoints, hrow]
    · refine ⟨⟨_, .north, _, ?_, hvw⟩, rfl, rfl⟩
      simp [gridNeighbor?, verticalPrimalEndpoints]

theorem ext {a b : GridDirectionalDart T} (hs : a.source = b.source)
    (hd : a.direction = b.direction) : a = b := by
  cases a with
  | mk asrc adir atgt astep aadj =>
      cases b with
      | mk bsrc bdir btgt bstep badj =>
          simp only at hs hd
          subst bsrc
          subst bdir
          have htgt : atgt = btgt := by
            rw [astep] at bstep
            exact Option.some.inj bstep
          subst btgt
          rfl

theorem ext_target {a b : GridDirectionalDart T} (ht : a.target = b.target)
    (hd : a.direction = b.direction) : a = b := by
  have ha := gridNeighbor?_opposite a.step
  have hb := gridNeighbor?_opposite b.step
  rw [ht, hd] at ha
  have hsource : a.source = b.source := Option.some.inj (ha.symm.trans hb)
  exact ext hsource hd

theorem ext_endpoints {a b : GridDirectionalDart T}
    (hs : a.source = b.source) (ht : a.target = b.target) : a = b := by
  have ha := a.step
  have hb := b.step
  rw [hs, ht] at ha
  have hd : a.direction = b.direction :=
    gridNeighbor?_direction_unique ha hb
  exact ext hs hd

instance : Finite (GridDirectionalDart T) :=
  Finite.of_injective
    (fun d : GridDirectionalDart T => (d.source, d.direction))
    (by
      intro a b h
      exact ext (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance [DecidableRel T.Adj] : Fintype (GridDirectionalDart T) :=
  Fintype.ofFinite _

instance : DecidableEq (GridDirectionalDart T) := by
  intro a b
  by_cases hs : a.source = b.source
  · by_cases hd : a.direction = b.direction
    · exact isTrue (ext hs hd)
    · exact isFalse (fun h => hd (congrArg GridDirectionalDart.direction h))
  · exact isFalse (fun h => hs (congrArg GridDirectionalDart.source h))

/-- Occupied outgoing compass directions at a vertex of `T`. -/
def directionsAt [DecidableRel T.Adj] (v : GridVertex m n) :
    Finset GridDirection :=
  Finset.univ.filter fun d =>
    ∃ w, gridNeighbor? v d = some w ∧ T.Adj v w

@[simp] theorem mem_directionsAt [DecidableRel T.Adj]
    {v : GridVertex m n} {d : GridDirection} :
    d ∈ directionsAt (T := T) v ↔
      ∃ w, gridNeighbor? v d = some w ∧ T.Adj v w := by
  simp [directionsAt]

/-- Reversal in source/direction coordinates. -/
def reverse (d : GridDirectionalDart T) : GridDirectionalDart T where
  source := d.target
  direction := d.direction.opposite
  target := d.source
  step := gridNeighbor?_opposite d.step
  adj := d.adj.symm

@[simp] theorem reverse_reverse (d : GridDirectionalDart T) :
    d.reverse.reverse = d := by
  apply ext <;> simp [reverse]

theorem reverse_direction_mem [DecidableRel T.Adj]
    (d : GridDirectionalDart T) :
    d.direction.opposite ∈ directionsAt (T := T) d.target := by
  rw [mem_directionsAt]
  exact ⟨d.source, gridNeighbor?_opposite d.step, d.adj.symm⟩

/-- The unique directional dart certified by membership in `directionsAt`. -/
noncomputable def ofDirectionMem [DecidableRel T.Adj]
    (v : GridVertex m n) (d : GridDirection)
    (h : d ∈ directionsAt (T := T) v) : GridDirectionalDart T := by
  rw [mem_directionsAt] at h
  exact ⟨v, d, h.choose, h.choose_spec.1, h.choose_spec.2⟩

@[simp] theorem ofDirectionMem_source [DecidableRel T.Adj]
    (v : GridVertex m n) (d : GridDirection)
    (h : d ∈ directionsAt (T := T) v) :
    (ofDirectionMem (T := T) v d h).source = v := rfl

@[simp] theorem ofDirectionMem_direction [DecidableRel T.Adj]
    (v : GridVertex m n) (d : GridDirection)
    (h : d ∈ directionsAt (T := T) v) :
    (ofDirectionMem (T := T) v d h).direction = d := rfl

/-- Boundary-contour successor: reverse the incoming direction at its target,
then take the next occupied tree direction clockwise. -/
noncomputable def contourSucc [DecidableRel T.Adj]
    (d : GridDirectionalDart T) : GridDirectionalDart T :=
  let incoming := d.direction.opposite
  let next := incoming.nextIn (directionsAt (T := T) d.target)
  ofDirectionMem (T := T) d.target next
    (GridDirection.nextIn_mem (reverse_direction_mem d))

@[simp] theorem contourSucc_source [DecidableRel T.Adj]
    (d : GridDirectionalDart T) : d.contourSucc.source = d.target := rfl

@[simp] theorem contourSucc_direction [DecidableRel T.Adj]
    (d : GridDirectionalDart T) :
    d.contourSucc.direction =
      d.direction.opposite.nextIn (directionsAt (T := T) d.target) := rfl

theorem contourSucc_ne [DecidableRel T.Adj]
    (d : GridDirectionalDart T) : d.contourSucc ≠ d := by
  intro h
  have hst : d.target = d.source := by
    simpa only [contourSucc_source] using congrArg GridDirectionalDart.source h
  exact T.loopless.irrefl d.source (hst ▸ d.adj)

/-- The local rotations make contour successor injective. -/
theorem contourSucc_injective [DecidableRel T.Adj] :
    Function.Injective (@contourSucc m n T _) := by
  intro a b h
  have ht : a.target = b.target := by
    simpa only [contourSucc_source] using
      congrArg GridDirectionalDart.source h
  have hdirNext :
      a.direction.opposite.nextIn (directionsAt (T := T) a.target) =
        b.direction.opposite.nextIn (directionsAt (T := T) a.target) := by
    have := congrArg GridDirectionalDart.direction h
    simpa only [contourSucc_direction, ht] using this
  have haMem : a.direction.opposite ∈ directionsAt (T := T) a.target :=
    reverse_direction_mem a
  have hbMem : b.direction.opposite ∈ directionsAt (T := T) a.target := by
    simpa only [ht] using reverse_direction_mem b
  have hopp := GridDirection.nextIn_injective_on
    (directionsAt (T := T) a.target) haMem hbMem hdirNext
  have hdir : a.direction = b.direction := by
    have := congrArg GridDirection.opposite hopp
    simpa using this
  exact ext_target ht hdir

/-- Contour successor as a permutation of the finite directed tree edges. -/
noncomputable def contourEquiv [DecidableRel T.Adj] :
    GridDirectionalDart T ≃ GridDirectionalDart T :=
  Equiv.ofBijective contourSucc
    ⟨contourSucc_injective, Finite.injective_iff_surjective.mp contourSucc_injective⟩

end GridDirectionalDart

end GridGraphs
