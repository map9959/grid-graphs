import GridGraphs.Diagonal

/-!
# The planar dual of a rectangular grid

This module supplies the combinatorial data used by the Python dual checker.
A face is either the unbounded face `out` or a bounded unit cell.  Horizontal
primal edges are oriented left-to-right and have dual endpoints (above, below);
vertical primal edges are oriented top-to-bottom and have dual endpoints
(left, right).  A side on the boundary is incident to `out`.

`uuDualGraph U` retains the dual edge crossing each primal edge whose two
endpoints belong to `U`.  It is a simple graph, so a degenerate grid edge whose
two sides are both `out` contributes no loop.

The finite row-ray parity argument proves that a forced primal cycle cuts off a
nonempty collection of bounded cells and no U-U edge crosses that face cut.
Consequently dual connectivity implies forced-primal acyclicity without relying
on general planar-embedding infrastructure.
-/

namespace GridGraphs

/-- Faces of an `m` by `n` grid: the unbounded face and its unit cells. -/
inductive GridFace (m n : Nat) where
  | out
  | cell (row : Fin (m - 1)) (col : Fin (n - 1))
  deriving DecidableEq, Fintype

/-- A horizontal grid edge, oriented from column `col` to `col + 1`. -/
structure HorizontalGridEdge (m n : Nat) where
  row : Fin m
  col : Fin (n - 1)
  deriving DecidableEq, Fintype

/-- A vertical grid edge, oriented from row `row` to `row + 1`. -/
structure VerticalGridEdge (m n : Nat) where
  row : Fin (m - 1)
  col : Fin n
  deriving DecidableEq, Fintype

/-- The two primal endpoints of an oriented horizontal edge. -/
def horizontalPrimalEndpoints {m n : Nat} (e : HorizontalGridEdge m n) :
    GridVertex m n × GridVertex m n :=
  ((e.row, ⟨e.col.val, by omega⟩),
    (e.row, ⟨e.col.val + 1, by omega⟩))

/-- The two primal endpoints of an oriented vertical edge. -/
def verticalPrimalEndpoints {m n : Nat} (e : VerticalGridEdge m n) :
    GridVertex m n × GridVertex m n :=
  ((⟨e.row.val, by omega⟩, e.col),
    (⟨e.row.val + 1, by omega⟩, e.col))

/-- Dual endpoints of a horizontal edge, ordered as (above, below). -/
def horizontalDualEndpoints {m n : Nat} (e : HorizontalGridEdge m n) :
    GridFace m n × GridFace m n :=
  (if h : e.row.val = 0 then
      .out
    else
      .cell ⟨e.row.val - 1, by omega⟩ e.col,
   if h : e.row.val + 1 = m then
      .out
    else
      .cell ⟨e.row.val, by omega⟩ e.col)

/-- Dual endpoints of a vertical edge, ordered as (left, right). -/
def verticalDualEndpoints {m n : Nat} (e : VerticalGridEdge m n) :
    GridFace m n × GridFace m n :=
  (if h : e.col.val = 0 then
      .out
    else
      .cell e.row ⟨e.col.val - 1, by omega⟩,
   if h : e.col.val + 1 = n then
      .out
    else
      .cell e.row ⟨e.col.val, by omega⟩)

@[simp] theorem horizontalDualEndpoints_fst_of_top {m n : Nat}
    (e : HorizontalGridEdge m n) (h : e.row.val = 0) :
    (horizontalDualEndpoints e).1 = GridFace.out := by
  simp [horizontalDualEndpoints, h]

@[simp] theorem horizontalDualEndpoints_snd_of_bottom {m n : Nat}
    (e : HorizontalGridEdge m n) (h : e.row.val + 1 = m) :
    (horizontalDualEndpoints e).2 = GridFace.out := by
  simp [horizontalDualEndpoints, h]

@[simp] theorem verticalDualEndpoints_fst_of_left {m n : Nat}
    (e : VerticalGridEdge m n) (h : e.col.val = 0) :
    (verticalDualEndpoints e).1 = GridFace.out := by
  simp [verticalDualEndpoints, h]

@[simp] theorem verticalDualEndpoints_snd_of_right {m n : Nat}
    (e : VerticalGridEdge m n) (h : e.col.val + 1 = n) :
    (verticalDualEndpoints e).2 = GridFace.out := by
  simp [verticalDualEndpoints, h]

theorem horizontalPrimalEndpoints_adj {m n : Nat} (e : HorizontalGridEdge m n) :
    (gridGraph m n).Adj (horizontalPrimalEndpoints e).1
      (horizontalPrimalEndpoints e).2 := by
  left
  exact ⟨rfl, Or.inl rfl⟩

theorem verticalPrimalEndpoints_adj {m n : Nat} (e : VerticalGridEdge m n) :
    (gridGraph m n).Adj (verticalPrimalEndpoints e).1
      (verticalPrimalEndpoints e).2 := by
  right
  exact ⟨rfl, Or.inl rfl⟩

/-- Every grid adjacency has a horizontal or vertical coordinate witness,
unique up to the orientation of its two endpoints. -/
theorem gridGraph_adj_exists_coordinate_edge {m n : Nat}
    {v w : GridVertex m n} (h : (gridGraph m n).Adj v w) :
    (∃ e : HorizontalGridEdge m n,
      (v = (horizontalPrimalEndpoints e).1 ∧
        w = (horizontalPrimalEndpoints e).2) ∨
      (v = (horizontalPrimalEndpoints e).2 ∧
        w = (horizontalPrimalEndpoints e).1)) ∨
    (∃ e : VerticalGridEdge m n,
      (v = (verticalPrimalEndpoints e).1 ∧
        w = (verticalPrimalEndpoints e).2) ∨
      (v = (verticalPrimalEndpoints e).2 ∧
        w = (verticalPrimalEndpoints e).1)) := by
  rcases h with ⟨hrow, hstep | hstep⟩ | ⟨hcol, hstep | hstep⟩
  · left
    let e : HorizontalGridEdge m n :=
      ⟨v.1, ⟨v.2.val, by omega⟩⟩
    refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
    · apply Prod.ext
      · exact hrow.symm.trans rfl
      · apply Fin.ext
        exact hstep.symm
  · left
    let e : HorizontalGridEdge m n :=
      ⟨w.1, ⟨w.2.val, by omega⟩⟩
    refine ⟨e, Or.inr ⟨?_, ?_⟩⟩
    · apply Prod.ext
      · exact hrow.trans rfl
      · apply Fin.ext
        exact hstep.symm
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
  · right
    let e : VerticalGridEdge m n :=
      ⟨⟨v.1.val, by omega⟩, v.2⟩
    refine ⟨e, Or.inl ⟨?_, ?_⟩⟩
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact hstep.symm
      · exact hcol.symm.trans rfl
  · right
    let e : VerticalGridEdge m n :=
      ⟨⟨w.1.val, by omega⟩, w.2⟩
    refine ⟨e, Or.inr ⟨?_, ?_⟩⟩
    · apply Prod.ext
      · apply Fin.ext
        exact hstep.symm
      · exact hcol.trans rfl
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl

/-- An ordered pair `(x,y)` is the unordered pair of endpoints in `p`. -/
def HasDualEndpoints {m n : Nat} (p : GridFace m n × GridFace m n)
    (x y : GridFace m n) : Prop :=
  (x = p.1 ∧ y = p.2) ∨ (x = p.2 ∧ y = p.1)

/-- A property invariant under swapping an unordered pair can be transported
from its named endpoints to any pair with those endpoints. -/
theorem hasDualEndpoints_iff {m n : Nat} {p : GridFace m n × GridFace m n}
    {x y : GridFace m n} (h : HasDualEndpoints p x y)
    (P : GridFace m n → Prop) :
    (P x ↔ P y) ↔ (P p.1 ↔ P p.2) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact iff_comm

/-- Adjacency generated by duals of horizontal and vertical U-U primal edges. -/
def UUDualAdj {m n : Nat} (U : Finset (GridVertex m n))
    (x y : GridFace m n) : Prop :=
  x ≠ y ∧
    ((∃ e : HorizontalGridEdge m n,
        (horizontalPrimalEndpoints e).1 ∈ U ∧
        (horizontalPrimalEndpoints e).2 ∈ U ∧
        HasDualEndpoints (horizontalDualEndpoints e) x y) ∨
      (∃ e : VerticalGridEdge m n,
        (verticalPrimalEndpoints e).1 ∈ U ∧
        (verticalPrimalEndpoints e).2 ∈ U ∧
        HasDualEndpoints (verticalDualEndpoints e) x y))

/-- The simple dual graph formed by primal edges with both endpoints in `U`. -/
def uuDualGraph {m n : Nat} (U : Finset (GridVertex m n)) :
    SimpleGraph (GridFace m n) where
  Adj := UUDualAdj U
  symm := by
    rintro x y ⟨hxy, h⟩
    refine ⟨Ne.symm hxy, ?_⟩
    rcases h with h | h
    · left
      rcases h with ⟨e, he₁, he₂, hends⟩
      exact ⟨e, he₁, he₂, hends.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)⟩
    · right
      rcases h with ⟨e, he₁, he₂, hends⟩
      exact ⟨e, he₁, he₂, hends.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless := by
    intro x h
    exact h.1 rfl

/-- Exact adjacency characterization for `uuDualGraph`. -/
@[simp] theorem uuDualGraph_adj {m n : Nat} (U : Finset (GridVertex m n))
    (x y : GridFace m n) :
    (uuDualGraph U).Adj x y ↔ UUDualAdj U x y :=
  Iff.rfl

/-- Fully expanded adjacency characterization: adjacent faces are precisely
the distinct sides of a horizontal or vertical primal edge internal to `U`. -/
theorem uuDualGraph_adj_iff {m n : Nat} (U : Finset (GridVertex m n))
    (x y : GridFace m n) :
    (uuDualGraph U).Adj x y ↔
      x ≠ y ∧
        ((∃ e : HorizontalGridEdge m n,
            (horizontalPrimalEndpoints e).1 ∈ U ∧
            (horizontalPrimalEndpoints e).2 ∈ U ∧
            HasDualEndpoints (horizontalDualEndpoints e) x y) ∨
          (∃ e : VerticalGridEdge m n,
            (verticalPrimalEndpoints e).1 ∈ U ∧
            (verticalPrimalEndpoints e).2 ∈ U ∧
            HasDualEndpoints (verticalDualEndpoints e) x y)) :=
  Iff.rfl

instance uuDualGraph_decidableRel {m n : Nat} (U : Finset (GridVertex m n)) :
    DecidableRel (uuDualGraph U).Adj := by
  intro x y
  simp only [uuDualGraph_adj, UUDualAdj, HasDualEndpoints]
  infer_instance

/-- Face adjacency through primal grid edges not used by the walk `c`.  Thus
reachability from `out` describes the faces on the unbounded side of `c`. -/
def cycleComplementDualGraph {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : SimpleGraph (GridFace m n) where
  Adj x y :=
    x ≠ y ∧
      ((∃ e : HorizontalGridEdge m n,
          s((horizontalPrimalEndpoints e).1,
            (horizontalPrimalEndpoints e).2) ∉ c.edges ∧
          HasDualEndpoints (horizontalDualEndpoints e) x y) ∨
        (∃ e : VerticalGridEdge m n,
          s((verticalPrimalEndpoints e).1,
            (verticalPrimalEndpoints e).2) ∉ c.edges ∧
          HasDualEndpoints (verticalDualEndpoints e) x y))
  symm := by
    rintro x y ⟨hxy, h⟩
    refine ⟨hxy.symm, ?_⟩
    rcases h with h | h
    · left
      obtain ⟨e, he, hends⟩ := h
      exact ⟨e, he, hends.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)⟩
    · right
      obtain ⟨e, he, hends⟩ := h
      exact ⟨e, he, hends.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless := by
    intro x h
    exact h.1 rfl

instance cycleComplementDualGraph_decidableRel {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : DecidableRel (cycleComplementDualGraph c).Adj := by
  intro x y
  simp only [cycleComplementDualGraph, HasDualEndpoints]
  infer_instance

/-- The finite set of bounded-side candidates: faces not reachable from `out`
without crossing an edge of `c`. -/
def cycleInteriorFaces {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : Finset (GridFace m n) :=
  Finset.univ.filter
    (fun f => ¬(cycleComplementDualGraph c).Reachable GridFace.out f)

@[simp] theorem mem_cycleInteriorFaces_iff {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (f : GridFace m n) :
    f ∈ cycleInteriorFaces c ↔
      ¬(cycleComplementDualGraph c).Reachable GridFace.out f := by
  simp [cycleInteriorFaces]

@[simp] theorem out_not_mem_cycleInteriorFaces {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : GridFace.out ∉ cycleInteriorFaces c := by
  simp

/-- Deleting a larger set of primal walk edges leaves a smaller dual
complement graph.  This is the basic cut monotonicity behind nested face
carriers. -/
theorem cycleComplementDualGraph_le_of_edges_subset {m n : Nat}
    {G H : SimpleGraph (GridVertex m n)}
    {a b c d : GridVertex m n} (p : G.Walk a b) (q : H.Walk c d)
    (hedges : ∀ e, e ∈ p.edges → e ∈ q.edges) :
    cycleComplementDualGraph q ≤ cycleComplementDualGraph p := by
  intro x y hxy
  rcases hxy with ⟨hne, hhorizontal | hvertical⟩
  · refine ⟨hne, Or.inl ?_⟩
    rcases hhorizontal with ⟨e, he, hends⟩
    exact ⟨e, fun hp => he (hedges _ hp), hends⟩
  · refine ⟨hne, Or.inr ?_⟩
    rcases hvertical with ⟨e, he, hends⟩
    exact ⟨e, fun hp => he (hedges _ hp), hends⟩

/-- Walk-edge inclusion induces inclusion of bounded dual-face carriers. -/
theorem cycleInteriorFaces_mono_of_edges_subset {m n : Nat}
    {G H : SimpleGraph (GridVertex m n)}
    {a b c d : GridVertex m n} (p : G.Walk a b) (q : H.Walk c d)
    (hedges : ∀ e, e ∈ p.edges → e ∈ q.edges) :
    cycleInteriorFaces p ⊆ cycleInteriorFaces q := by
  intro f hf
  rw [mem_cycleInteriorFaces_iff] at hf ⊢
  intro hreach
  obtain ⟨w⟩ := hreach
  exact hf ⟨w.map (.ofLE
    (cycleComplementDualGraph_le_of_edges_subset p q hedges))⟩

/-- `cycleInteriorFaces` depends only on the undirected edge membership of its
walk, independently of base point, orientation, repetition order, or ambient
subgraph proofs. -/
theorem cycleInteriorFaces_eq_of_edges_membership_iff {m n : Nat}
    {G H : SimpleGraph (GridVertex m n)}
    {a b c d : GridVertex m n} (p : G.Walk a b) (q : H.Walk c d)
    (hedges : ∀ e, e ∈ p.edges ↔ e ∈ q.edges) :
    cycleInteriorFaces p = cycleInteriorFaces q := by
  apply Finset.Subset.antisymm
  · exact cycleInteriorFaces_mono_of_edges_subset p q
      (fun e he => (hedges e).1 he)
  · exact cycleInteriorFaces_mono_of_edges_subset q p
      (fun e he => (hedges e).2 he)

/-- Exact dual-reachability obligation for inclusion of two face carriers. -/
theorem cycleInteriorFaces_subset_iff_reachable_transport {m n : Nat}
    {G H : SimpleGraph (GridVertex m n)}
    {a b c d : GridVertex m n} (p : G.Walk a b) (q : H.Walk c d) :
    cycleInteriorFaces p ⊆ cycleInteriorFaces q ↔
      ∀ f, (cycleComplementDualGraph q).Reachable GridFace.out f →
        (cycleComplementDualGraph p).Reachable GridFace.out f := by
  constructor
  · intro hsubset f hq
    by_contra hp
    have hfp : f ∈ cycleInteriorFaces p :=
      (mem_cycleInteriorFaces_iff p f).2 hp
    have hfq := hsubset hfp
    exact (mem_cycleInteriorFaces_iff q f).1 hfq hq
  · intro htransport f hfp
    rw [mem_cycleInteriorFaces_iff] at hfp ⊢
    intro hq
    exact hfp (htransport f hq)

/-- Exact dual-reachability obligation for disjointness of two face carriers. -/
theorem cycleInteriorFaces_disjoint_iff_reachable_exterior {m n : Nat}
    {G H : SimpleGraph (GridVertex m n)}
    {a b c d : GridVertex m n} (p : G.Walk a b) (q : H.Walk c d) :
    Disjoint (cycleInteriorFaces p) (cycleInteriorFaces q) ↔
      ∀ f, ¬(cycleComplementDualGraph p).Reachable GridFace.out f →
        (cycleComplementDualGraph q).Reachable GridFace.out f := by
  rw [Finset.disjoint_left]
  constructor
  · intro h f hp
    by_contra hq
    exact h ((mem_cycleInteriorFaces_iff p f).2 hp)
      ((mem_cycleInteriorFaces_iff q f).2 hq)
  · intro h f hfp hfq
    exact (mem_cycleInteriorFaces_iff q f).1 hfq
      (h f ((mem_cycleInteriorFaces_iff p f).1 hfp))

/-- Adjoining one edge to the right endpoint does not change reachability from
a fixed source. -/
theorem reachable_right_iff_of_adj {V : Type*} {G : SimpleGraph V}
    {a x y : V} (hxy : G.Adj x y) :
    G.Reachable a x ↔ G.Reachable a y := by
  constructor
  · intro h
    exact h.trans hxy.reachable
  · intro h
    exact h.trans hxy.symm.reachable

/-- If a horizontal primal edge is not used by `c`, its two incident faces
have the same bounded-side membership.  Boundary degeneracies are handled by
the equality case. -/
theorem horizontal_mem_cycleInteriorFaces_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : HorizontalGridEdge m n)
    (he : s((horizontalPrimalEndpoints e).1,
      (horizontalPrimalEndpoints e).2) ∉ c.edges) :
    (horizontalDualEndpoints e).1 ∈ cycleInteriorFaces c ↔
      (horizontalDualEndpoints e).2 ∈ cycleInteriorFaces c := by
  by_cases hsame : (horizontalDualEndpoints e).1 = (horizontalDualEndpoints e).2
  · rw [hsame]
  · simp only [mem_cycleInteriorFaces_iff]
    rw [not_iff_not]
    exact reachable_right_iff_of_adj ⟨hsame, Or.inl ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Vertical counterpart of
`horizontal_mem_cycleInteriorFaces_iff_of_not_mem_edges`. -/
theorem vertical_mem_cycleInteriorFaces_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    (verticalDualEndpoints e).1 ∈ cycleInteriorFaces c ↔
      (verticalDualEndpoints e).2 ∈ cycleInteriorFaces c := by
  by_cases hsame : (verticalDualEndpoints e).1 = (verticalDualEndpoints e).2
  · rw [hsame]
  · simp only [mem_cycleInteriorFaces_iff]
    rw [not_iff_not]
    exact reachable_right_iff_of_adj ⟨hsame, Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A horizontal U-U edge cannot occur in a walk of the forced graph of
`Uᶜ`: every forced edge has at least one endpoint outside `U`. -/
theorem horizontal_not_mem_forcedCycle_edges {m n : Nat}
    (U : Finset (GridVertex m n)) {v w : GridVertex m n}
    (c : (forcedEdgeGraph (gridGraph m n)
      (↑U : Set (GridVertex m n))ᶜ).Walk v w)
    (e : HorizontalGridEdge m n)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ U)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ U) :
    s((horizontalPrimalEndpoints e).1,
      (horizontalPrimalEndpoints e).2) ∉ c.edges := by
  intro he
  rcases (c.adj_of_mem_edges he).2 with hout | hout
  · exact hout he₁
  · exact hout he₂

/-- Vertical counterpart of `horizontal_not_mem_forcedCycle_edges`. -/
theorem vertical_not_mem_forcedCycle_edges {m n : Nat}
    (U : Finset (GridVertex m n)) {v w : GridVertex m n}
    (c : (forcedEdgeGraph (gridGraph m n)
      (↑U : Set (GridVertex m n))ᶜ).Walk v w)
    (e : VerticalGridEdge m n)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ U)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ U) :
    s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges := by
  intro he
  rcases (c.adj_of_mem_edges he).2 with hout | hout
  · exact hout he₁
  · exact hout he₂

/-- Standard finite-grid enclosure statement left by the reachability
construction: deleting the primal edges of a simple grid cycle leaves at least
one face unreachable from the unbounded face.  Since `out` is always reachable
from itself, any member supplied here is automatically a bounded cell. -/
def GridCycleEnclosesBoundedFace : Prop :=
  ∀ {m n : Nat} (U : Finset (GridVertex m n))
    {v : GridVertex m n}
    (c : (forcedEdgeGraph (gridGraph m n)
      (↑U : Set (GridVertex m n))ᶜ).Walk v v),
    c.IsCycle → (cycleInteriorFaces c).Nonempty

/-- Number of steps of a walk crossing a Boolean vertex cut.  This recursive
form is convenient for parity induction and does not require converting the
walk's edge multiset to an auxiliary graph. -/
def walkCutCrossings {V : Type*} {G : SimpleGraph V} (side : V → Bool) :
    {u v : V} → G.Walk u v → Nat
  | _, _, .nil => 0
  | u, _, .cons _ p => (if side u = side (p.getVert 0) then 0 else 1) +
      walkCutCrossings side p

/-- A walk crosses a Boolean cut evenly exactly when its endpoints are on the
same side. -/
theorem even_walkCutCrossings_iff {V : Type*} {G : SimpleGraph V}
    (side : V → Bool) {u v : V} (p : G.Walk u v) :
    Even (walkCutCrossings side p) ↔ side u = side v := by
  induction p with
  | nil => simp [walkCutCrossings]
  | @cons u x v h p ih =>
      cases hu : side u <;> cases hx : side x <;> cases hv : side v <;>
        simp_all [walkCutCrossings]

/-- In particular, every closed walk crosses every finite or infinite Boolean
vertex cut an even number of times. -/
theorem even_walkCutCrossings_of_isClosed {V : Type*} {G : SimpleGraph V}
    (side : V → Bool) {v : V} (c : G.Walk v v) :
    Even (walkCutCrossings side c) := by
  exact (even_walkCutCrossings_iff side c).2 rfl

/-- An unordered edge crosses a Boolean cut when its endpoint-image is the
unique two-element Boolean edge. -/
def EdgeCrossesBoolCut {V : Type*} (side : V → Bool) (e : Sym2 V) : Bool :=
  decide (e.map side = s(false, true))

@[simp] theorem edgeCrossesBoolCut_s {V : Type*} (side : V → Bool) (x y : V) :
    EdgeCrossesBoolCut side s(x, y) = true ↔ side x ≠ side y := by
  cases hx : side x <;> cases hy : side y <;>
    simp [EdgeCrossesBoolCut, hx, hy]

/-- The recursive crossing count is the filtered count of unordered walk
edges. -/
theorem walkCutCrossings_eq_countP_edges {V : Type*} {G : SimpleGraph V}
    (side : V → Bool) {u v : V} (p : G.Walk u v) :
    walkCutCrossings side p = p.edges.countP (EdgeCrossesBoolCut side) := by
  induction p with
  | nil => simp [walkCutCrossings]
  | @cons u x v h p ih =>
      simp only [walkCutCrossings, SimpleGraph.Walk.edges_cons, List.countP_cons,
        edgeCrossesBoolCut_s, ih]
      by_cases hs : side u = side x
      · simp [hs]
      · simp [hs, Nat.add_comm]

/-- Boolean cut consisting of grid vertices weakly above a row boundary. -/
def gridRowPrefixSide {m n : Nat} (row : Fin (m - 1))
    (x : GridVertex m n) : Bool :=
  decide (x.1.val ≤ row.val)

/-- Boolean cut consisting of grid vertices weakly left of a column boundary. -/
def gridColumnPrefixSide {m n : Nat} (col : Fin (n - 1))
    (x : GridVertex m n) : Bool :=
  decide (x.2.val ≤ col.val)

/-- Closed-walk conservation across a complete horizontal grid cut. -/
theorem even_gridRowPrefix_crossings {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (c : G.Walk v v) (row : Fin (m - 1)) :
    Even (walkCutCrossings (gridRowPrefixSide row) c) :=
  even_walkCutCrossings_of_isClosed _ c

/-- Closed-walk conservation across a complete vertical grid cut. -/
theorem even_gridColumnPrefix_crossings {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (c : G.Walk v v) (col : Fin (n - 1)) :
    Even (walkCutCrossings (gridColumnPrefixSide col) c) :=
  even_walkCutCrossings_of_isClosed _ c

@[simp] theorem horizontal_edge_not_crosses_gridRowPrefixSide {m n : Nat}
    (row : Fin (m - 1)) (e : HorizontalGridEdge m n) :
    EdgeCrossesBoolCut (gridRowPrefixSide row)
      s((horizontalPrimalEndpoints e).1,
        (horizontalPrimalEndpoints e).2) = false := by
  apply Bool.eq_false_iff.mpr
  simp [gridRowPrefixSide, horizontalPrimalEndpoints]

@[simp] theorem vertical_edge_crosses_gridRowPrefixSide_iff {m n : Nat}
    (row : Fin (m - 1)) (e : VerticalGridEdge m n) :
    EdgeCrossesBoolCut (gridRowPrefixSide row)
      s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2) = true ↔ e.row = row := by
  rw [edgeCrossesBoolCut_s]
  simp only [gridRowPrefixSide, verticalPrimalEndpoints]
  constructor
  · intro h
    apply Fin.ext
    simp only [ne_eq] at h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have : e.row.val + 1 ≤ row.val := by omega
      simp [show e.row.val ≤ row.val by omega, this] at h
    · have : row.val < e.row.val := by omega
      simp [show ¬e.row.val ≤ row.val by omega,
        show ¬e.row.val + 1 ≤ row.val by omega] at h
  · rintro rfl
    simp

/-- Every vertex has even incidence count in the edge list of a grid cycle.
This is the local conservation law used at horizontal ray endpoints. -/
theorem gridCycle_even_incident_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    {c : G.Walk v v} (hc : c.IsCycle) (x : GridVertex m n) :
    Even (c.edges.countP fun e => x ∈ e) := by
  apply (hc.isTrail.even_countP_edges_iff x).2
  intro hvv
  exact (hvv rfl).elim

/-- Vertical cycle edges crossing the leftward horizontal ray from the center
of cell `(row,col)`.  The ray crosses vertical grid line `e.col` exactly when
`e.col ≤ col`; requiring `e.row = row` selects its row interval. -/
def rowRayCrossingEdges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (row : Fin (m - 1)) (col : Fin (n - 1)) :
    Finset (VerticalGridEdge m n) :=
  Finset.univ.filter fun e =>
    s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges ∧
    e.row = row ∧ e.col.val ≤ col.val

@[simp] theorem mem_rowRayCrossingEdges_iff {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (row : Fin (m - 1)) (col : Fin (n - 1))
    (e : VerticalGridEdge m n) :
    e ∈ rowRayCrossingEdges c row col ↔
      s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2) ∈ c.edges ∧
      e.row = row ∧ e.col.val ≤ col.val := by
  simp [rowRayCrossingEdges]

/-- Row-ray parity for a face.  The unbounded face has parity zero; a bounded
cell is odd when its leftward ray crosses an odd number of vertical cycle
edges. -/
def FaceRowRayOdd {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : GridFace m n → Prop
  | .out => False
  | .cell row col => Odd (rowRayCrossingEdges c row col).card

instance faceRowRayOdd_decidable {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : DecidablePred (FaceRowRayOdd c) := by
  intro f
  cases f with
  | out => exact isFalse (by simp [FaceRowRayOdd])
  | cell row col =>
      simp only [FaceRowRayOdd]
      infer_instance

@[simp] theorem faceRowRayOdd_out {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) : ¬FaceRowRayOdd c GridFace.out := by
  simp [FaceRowRayOdd]

/-- Two vertical coordinate edges with the same row and column are equal. -/
theorem verticalGridEdge_eq_of_row_eq_of_col_val_eq {m n : Nat}
    {e e' : VerticalGridEdge m n} (hr : e.row = e'.row)
    (hc : e.col.val = e'.col.val) : e = e' := by
  cases e with
  | mk er ec =>
      cases e' with
      | mk er' ec' =>
          simp only [VerticalGridEdge.mk.injEq]
          exact ⟨hr, Fin.ext hc⟩

/-- The unordered primal endpoints determine a vertical coordinate edge. -/
theorem verticalPrimalEndpoints_sym2_injective {m n : Nat} :
    Function.Injective (fun e : VerticalGridEdge m n =>
      s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2)) := by
  intro e e' h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply verticalGridEdge_eq_of_row_eq_of_col_val_eq
    · apply Fin.ext
      simpa [verticalPrimalEndpoints] using congrArg (fun x => x.1.val) h.1
    · simpa [verticalPrimalEndpoints] using congrArg (fun x => x.2.val) h.1
  · have hrow : e.row.val = e'.row.val + 1 := by
      simpa [verticalPrimalEndpoints] using congrArg (fun x => x.1.val) h.1
    have hrow' : e.row.val + 1 = e'.row.val := by
      simpa [verticalPrimalEndpoints] using congrArg (fun x => x.1.val) h.2
    omega

/-- Predicate on unordered primal edges corresponding to a bounded leftward
row ray. -/
def EdgeCrossesRowRay {m n : Nat} (row : Fin (m - 1)) (col : Fin (n - 1))
    (e : Sym2 (GridVertex m n)) : Bool :=
  decide (∃ a : VerticalGridEdge m n,
    e = s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) ∧
      a.row = row ∧ a.col.val ≤ col.val)

/-- For a trail, filtering its unordered edge list by a row ray counts exactly
the coordinate edges in `rowRayCrossingEdges`. -/
theorem countP_edgeCrossesRowRay_eq_card {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    {c : G.Walk v w} (hc : c.IsTrail) (row : Fin (m - 1))
    (col : Fin (n - 1)) :
    c.edges.countP (EdgeCrossesRowRay row col) =
      (rowRayCrossingEdges c row col).card := by
  let edgeOf : VerticalGridEdge m n → Sym2 (GridVertex m n) := fun a =>
    s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2)
  have himage :
      (rowRayCrossingEdges c row col).image edgeOf =
        hc.edgesFinset.filter (fun e => EdgeCrossesRowRay row col e = true) := by
    ext e
    simp only [Finset.mem_image, mem_rowRayCrossingEdges_iff,
      Finset.mem_filter, Finset.mem_mk, Multiset.mem_coe]
    constructor
    · rintro ⟨a, ⟨ha, har, hac⟩, rfl⟩
      refine ⟨ha, ?_⟩
      simp only [EdgeCrossesRowRay, decide_eq_true_eq]
      exact ⟨a, rfl, har, hac⟩
    · rintro ⟨he, hray⟩
      simp only [EdgeCrossesRowRay, decide_eq_true_eq] at hray
      obtain ⟨a, rfl, har, hac⟩ := hray
      exact ⟨a, ⟨he, har, hac⟩, rfl⟩
  rw [← Finset.card_image_of_injective (rowRayCrossingEdges c row col)
    verticalPrimalEndpoints_sym2_injective, himage]
  rw [List.countP_eq_length_filter]
  have hfilter :
      (c.edges.filter (EdgeCrossesRowRay row col)).toFinset =
        hc.edgesFinset.filter (fun e => EdgeCrossesRowRay row col e = true) := by
    ext e
    simp
  rw [← hfilter, List.toFinset_card_of_nodup
    (hc.edges_nodup.filter (EdgeCrossesRowRay row col))]

@[simp] theorem edgeCrossesRowRay_horizontal {m n : Nat}
    (row : Fin (m - 1)) (col : Fin (n - 1)) (a : HorizontalGridEdge m n) :
    EdgeCrossesRowRay row col
      s((horizontalPrimalEndpoints a).1, (horizontalPrimalEndpoints a).2) = false := by
  rw [Bool.eq_false_iff]
  intro hcross
  simp only [EdgeCrossesRowRay, decide_eq_true_eq] at hcross
  obtain ⟨b, h, _, _⟩ := hcross
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have h₁ := congrArg (fun x : GridVertex m n => x.1.val) h.1
    have h₂ := congrArg (fun x : GridVertex m n => x.1.val) h.2
    simp [horizontalPrimalEndpoints, verticalPrimalEndpoints] at h₁ h₂
    omega
  · have h₁ := congrArg (fun x : GridVertex m n => x.1.val) h.1
    have h₂ := congrArg (fun x : GridVertex m n => x.1.val) h.2
    simp [horizontalPrimalEndpoints, verticalPrimalEndpoints] at h₁ h₂
    omega

@[simp] theorem edgeCrossesRowRay_vertical {m n : Nat}
    (row : Fin (m - 1)) (col : Fin (n - 1)) (a : VerticalGridEdge m n) :
    EdgeCrossesRowRay row col
      s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) = true ↔
        a.row = row ∧ a.col.val ≤ col.val := by
  simp only [EdgeCrossesRowRay, decide_eq_true_eq]
  constructor
  · rintro ⟨b, hab, hbr, hbc⟩
    have : b = a := verticalPrimalEndpoints_sym2_injective hab.symm
    subst b
    exact ⟨hbr, hbc⟩
  · rintro ⟨har, hac⟩
    exact ⟨a, rfl, har, hac⟩

/-- Boolean side consisting of one leftward horizontal segment of grid
vertices. -/
def gridHorizontalSegmentSide {m n : Nat} (row : Fin m) (col : Fin (n - 1))
    (x : GridVertex m n) : Bool :=
  decide (x.1 = row ∧ x.2.val ≤ col.val)

@[simp] theorem horizontal_edge_crosses_horizontalSegment_iff {m n : Nat}
    (row : Fin m) (col : Fin (n - 1)) (a : HorizontalGridEdge m n) :
    EdgeCrossesBoolCut (gridHorizontalSegmentSide row col)
      s((horizontalPrimalEndpoints a).1,
        (horizontalPrimalEndpoints a).2) = true ↔
      a.row = row ∧ a.col = col := by
  rw [edgeCrossesBoolCut_s]
  simp only [gridHorizontalSegmentSide, horizontalPrimalEndpoints]
  constructor
  · intro h
    by_cases har : a.row = row
    · refine ⟨har, ?_⟩
      apply Fin.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · simp [har, show a.col.val ≤ col.val by omega,
          show a.col.val + 1 ≤ col.val by omega] at h
      · simp [show ¬a.col.val ≤ col.val by omega,
          show ¬a.col.val + 1 ≤ col.val by omega] at h
    · simp [har] at h
  · rintro ⟨rfl, rfl⟩
    simp

@[simp] theorem vertical_edge_crosses_horizontalSegment_iff {m n : Nat}
    (row : Fin m) (col : Fin (n - 1)) (a : VerticalGridEdge m n) :
    EdgeCrossesBoolCut (gridHorizontalSegmentSide row col)
      s((verticalPrimalEndpoints a).1,
        (verticalPrimalEndpoints a).2) = true ↔
      a.col.val ≤ col.val ∧
        (a.row.val = row.val ∨ a.row.val + 1 = row.val) := by
  rw [edgeCrossesBoolCut_s]
  simp only [gridHorizontalSegmentSide, verticalPrimalEndpoints]
  constructor
  · intro h
    by_cases hac : a.col.val ≤ col.val
    · refine ⟨hac, ?_⟩
      by_contra hr
      push_neg at hr
      simp [hac, show (⟨a.row.val, by omega⟩ : Fin m) ≠ row by
          exact fun he => hr.1 (congrArg Fin.val he),
        show (⟨a.row.val + 1, by omega⟩ : Fin m) ≠ row by
          exact fun he => hr.2 (congrArg Fin.val he)] at h
    · simp [hac] at h
  · rintro ⟨hac, hr | hr⟩
    · have hnext : (⟨a.row.val + 1, by omega⟩ : Fin m) ≠ row := by
        intro he
        have := congrArg Fin.val he
        simp at this
        omega
      have hprev : (⟨a.row.val, by omega⟩ : Fin m) = row := by
        apply Fin.ext
        exact hr
      simp [hac, hprev, hnext]
    · have hprev : (⟨a.row.val, by omega⟩ : Fin m) ≠ row := by
        intro he
        have := congrArg Fin.val he
        simp at this
        omega
      have hnext : (⟨a.row.val + 1, by omega⟩ : Fin m) = row := by
        apply Fin.ext
        exact hr
      simp [hac, hnext, hprev]

/-- Row-ray crossing predicate extended by zero on the unbounded face. -/
def FaceRowRayCrossesEdge {m n : Nat} (f : GridFace m n)
    (e : Sym2 (GridVertex m n)) : Bool :=
  match f with
  | .out => false
  | .cell row col => EdgeCrossesRowRay row col e

theorem horizontalDual_rowRay_xor_on_horizontal_edge {m n : Nat}
    (e a : HorizontalGridEdge m n)
    (hne : s((horizontalPrimalEndpoints a).1,
        (horizontalPrimalEndpoints a).2) ≠
      s((horizontalPrimalEndpoints e).1,
        (horizontalPrimalEndpoints e).2)) :
    (FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
        s((horizontalPrimalEndpoints a).1, (horizontalPrimalEndpoints a).2) !=
      FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
        s((horizontalPrimalEndpoints a).1, (horizontalPrimalEndpoints a).2)) =
      EdgeCrossesBoolCut (gridHorizontalSegmentSide e.row e.col)
        s((horizontalPrimalEndpoints a).1, (horizontalPrimalEndpoints a).2) := by
  have hcross : EdgeCrossesBoolCut (gridHorizontalSegmentSide e.row e.col)
      s((horizontalPrimalEndpoints a).1,
        (horizontalPrimalEndpoints a).2) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨har, hac⟩ :=
      (horizontal_edge_crosses_horizontalSegment_iff e.row e.col a).mp h
    apply hne
    cases a
    cases e
    simp_all
  have hface (f : GridFace m n) : FaceRowRayCrossesEdge f
      s((horizontalPrimalEndpoints a).1,
        (horizontalPrimalEndpoints a).2) = false := by
    cases f with
    | out => rfl
    | cell row col => exact edgeCrossesRowRay_horizontal row col a
  simp [hface, hcross]

theorem horizontalDual_fst_crosses_vertical_iff {m n : Nat}
    (e : HorizontalGridEdge m n) (a : VerticalGridEdge m n) :
    FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
        s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) = true ↔
      a.col.val ≤ e.col.val ∧ a.row.val + 1 = e.row.val := by
  simp only [horizontalDualEndpoints]
  split_ifs with htop
  · simp only [FaceRowRayCrossesEdge, Bool.false_eq_true, false_iff]
    omega
  · simp only [FaceRowRayCrossesEdge]
    rw [edgeCrossesRowRay_vertical]
    constructor
    · rintro ⟨har, hac⟩
      refine ⟨hac, ?_⟩
      have := congrArg Fin.val har
      simp at this
      omega
    · rintro ⟨hac, har⟩
      exact ⟨Fin.ext (by simp; omega), hac⟩

theorem horizontalDual_snd_crosses_vertical_iff {m n : Nat}
    (e : HorizontalGridEdge m n) (a : VerticalGridEdge m n) :
    FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
        s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) = true ↔
      a.col.val ≤ e.col.val ∧ a.row.val = e.row.val := by
  simp only [horizontalDualEndpoints]
  split_ifs with hbottom
  · simp only [FaceRowRayCrossesEdge, Bool.false_eq_true, false_iff]
    omega
  · simp only [FaceRowRayCrossesEdge]
    rw [edgeCrossesRowRay_vertical]
    constructor
    · rintro ⟨har, hac⟩
      exact ⟨hac, congrArg Fin.val har⟩
    · rintro ⟨hac, har⟩
      exact ⟨Fin.ext har, hac⟩

theorem horizontalDual_rowRay_xor_on_vertical_edge {m n : Nat}
    (e : HorizontalGridEdge m n) (a : VerticalGridEdge m n) :
    (FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
        s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) !=
      FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
        s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2)) =
      EdgeCrossesBoolCut (gridHorizontalSegmentSide e.row e.col)
        s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.bne_eq_xor, Bool.xor_iff_ne,
    show (FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
          s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) ≠
        FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
          s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2)) ↔
        ((FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
            s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) = true) ≠
          (FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
            s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) = true)) by
      cases FaceRowRayCrossesEdge (horizontalDualEndpoints e).1
          s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) <;>
        cases FaceRowRayCrossesEdge (horizontalDualEndpoints e).2
          s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2) <;> simp,
    horizontalDual_fst_crosses_vertical_iff,
    horizontalDual_snd_crosses_vertical_iff,
    vertical_edge_crosses_horizontalSegment_iff]
  by_cases hac : a.col.val ≤ e.col.val <;>
    by_cases habove : a.row.val + 1 = e.row.val <;>
      by_cases hbelow : a.row.val = e.row.val <;> simp_all

theorem faceRowRayOdd_iff_odd_countP {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    {c : G.Walk v w} (hc : c.IsTrail) (f : GridFace m n) :
    FaceRowRayOdd c f ↔ Odd (c.edges.countP (FaceRowRayCrossesEdge f)) := by
  cases f with
  | out =>
      change False ↔ Odd (c.edges.countP fun _ => false)
      simp
  | cell row col =>
      change Odd (rowRayCrossingEdges c row col).card ↔
        Odd (c.edges.countP (EdgeCrossesRowRay row col))
      rw [countP_edgeCrossesRowRay_eq_card hc]

theorem List.countP_congr_of_forall_mem {α : Type*} (l : List α)
    (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [List.countP_cons, List.countP_cons, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]

/-- Counts of two Boolean predicates have the same parity when their pointwise
exclusive-or count is even. -/
theorem odd_countP_iff_of_even_xor {α : Type*} (l : List α) (p q : α → Bool)
    (hxor : Even (l.countP fun x => p x != q x)) :
    Odd (l.countP p) ↔ Odd (l.countP q) := by
  have hcount : l.countP p + l.countP q =
      l.countP (fun x => p x != q x) +
        2 * l.countP (fun x => p x && q x) := by
    clear hxor
    induction l with
    | nil => simp
    | cons x l ih =>
        cases hp : p x <;> cases hq : q x <;>
          simp_all <;> omega
  have hevenSum : Even (l.countP p + l.countP q) := by
    rw [hcount]
    exact hxor.add (even_two_mul _)
  rw [Nat.even_add] at hevenSum
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
  exact not_congr hevenSum

theorem odd_countP_or_odd_countP_of_odd_xor {α : Type*} (l : List α)
    (p q : α → Bool) (hxor : Odd (l.countP fun x => p x != q x)) :
    Odd (l.countP p) ∨ Odd (l.countP q) := by
  have hcount : l.countP p + l.countP q =
      l.countP (fun x => p x != q x) +
        2 * l.countP (fun x => p x && q x) := by
    clear hxor
    induction l with
    | nil => simp
    | cons x l ih =>
        cases hp : p x <;> cases hq : q x <;> simp_all <;> omega
  have hsum : Odd (l.countP p + l.countP q) := by
    rw [hcount]
    exact hxor.add_even (even_two_mul _)
  rw [Nat.odd_add] at hsum
  by_cases hp : Odd (l.countP p)
  · exact Or.inl hp
  · right
    exact Nat.not_even_iff_odd.mp (fun hq => hp (hsum.mpr hq))

theorem List.countP_add_one_eq_of_eq_except {α : Type*} [DecidableEq α]
    (l : List α) (a : α) (p q : α → Bool) (hn : l.Nodup) (ha : a ∈ l)
    (hp : p a = false) (hq : q a = true)
    (heq : ∀ x ∈ l, x ≠ a → p x = q x) :
    l.countP p + 1 = l.countP q := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      rw [List.nodup_cons] at hn
      by_cases hxa : x = a
      · subst x
        have htail : l.countP p = l.countP q :=
          List.countP_congr_of_forall_mem l p q fun y hy =>
            heq y (by simp [hy]) (fun hya => hn.1 (hya ▸ hy))
        simp [hp, hq, htail]
      · have hal : a ∈ l := by
          simp only [List.mem_cons] at ha
          rcases ha with hax | hal
          · exact (hxa hax.symm).elim
          · exact hal
        have hx : p x = q x := heq x (by simp) hxa
        have hi := ih hn.2 hal (fun y hy hya => heq y (by simp [hy]) hya)
        simp only [List.countP_cons, hx]
        omega

/-- Horizontal non-cycle edges preserve row-ray parity.  The relevant Boolean
cut is the finite horizontal segment ending at the edge's left endpoint. -/
theorem faceRowRayOdd_horizontal_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : HorizontalGridEdge m n)
    (he : s((horizontalPrimalEndpoints e).1,
      (horizontalPrimalEndpoints e).2) ∉ c.edges) :
    FaceRowRayOdd c (horizontalDualEndpoints e).1 ↔
      FaceRowRayOdd c (horizontalDualEndpoints e).2 := by
  rw [faceRowRayOdd_iff_odd_countP hc.isTrail,
    faceRowRayOdd_iff_odd_countP hc.isTrail]
  apply odd_countP_iff_of_even_xor
  have hcount : c.edges.countP (fun x =>
      FaceRowRayCrossesEdge (horizontalDualEndpoints e).1 x !=
        FaceRowRayCrossesEdge (horizontalDualEndpoints e).2 x) =
      c.edges.countP (EdgeCrossesBoolCut
        (gridHorizontalSegmentSide e.row e.col)) := by
    apply List.countP_congr_of_forall_mem
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hadj : (gridGraph m n).Adj x y := hG (c.adj_of_mem_edges hedge)
        rcases gridGraph_adj_exists_coordinate_edge hadj with h | h
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · apply horizontalDual_rowRay_xor_on_horizontal_edge
            intro hae
            apply he
            rw [← hae]
            exact hedge
          · rw [Sym2.eq_swap]
            apply horizontalDual_rowRay_xor_on_horizontal_edge
            intro hae
            apply he
            rw [← hae, Sym2.eq_swap]
            exact hedge
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · exact horizontalDual_rowRay_xor_on_vertical_edge e a
          · simpa only [Sym2.eq_swap] using
              horizontalDual_rowRay_xor_on_vertical_edge e a
  rw [hcount, ← walkCutCrossings_eq_countP_edges]
  exact even_walkCutCrossings_of_isClosed _ c

/-- The two incident face parities differ across a horizontal cycle edge. -/
theorem faceRowRayOdd_horizontal_or_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : HorizontalGridEdge m n)
    (he : s((horizontalPrimalEndpoints e).1,
      (horizontalPrimalEndpoints e).2) ∈ c.edges) :
    FaceRowRayOdd c (horizontalDualEndpoints e).1 ∨
      FaceRowRayOdd c (horizontalDualEndpoints e).2 := by
  rw [faceRowRayOdd_iff_odd_countP hc.isTrail,
    faceRowRayOdd_iff_odd_countP hc.isTrail]
  apply odd_countP_or_odd_countP_of_odd_xor
  let target := s((horizontalPrimalEndpoints e).1,
    (horizontalPrimalEndpoints e).2)
  let p := fun x =>
    FaceRowRayCrossesEdge (horizontalDualEndpoints e).1 x !=
      FaceRowRayCrossesEdge (horizontalDualEndpoints e).2 x
  let q := EdgeCrossesBoolCut (gridHorizontalSegmentSide e.row e.col)
  have hp : p target = false := by
    have hface (f : GridFace m n) : FaceRowRayCrossesEdge f target = false := by
      cases f with
      | out => rfl
      | cell row col => exact edgeCrossesRowRay_horizontal row col e
    simp [p, hface]
  have hq : q target = true := by
    exact (horizontal_edge_crosses_horizontalSegment_iff e.row e.col e).mpr
      ⟨rfl, rfl⟩
  have heq : ∀ x ∈ c.edges, x ≠ target → p x = q x := by
    intro edge hedge hne
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hadj := hG (c.adj_of_mem_edges hedge)
        rcases gridGraph_adj_exists_coordinate_edge hadj with h | h
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · simpa [p, q, target] using
              horizontalDual_rowRay_xor_on_horizontal_edge e a hne
          · rw [Sym2.eq_swap]
            simpa [p, q, target, Sym2.eq_swap] using
              horizontalDual_rowRay_xor_on_horizontal_edge e a
                (by simpa only [Sym2.eq_swap] using hne)
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · simpa [p, q] using horizontalDual_rowRay_xor_on_vertical_edge e a
          · simpa [p, q, Sym2.eq_swap] using
              horizontalDual_rowRay_xor_on_vertical_edge e a
  have hdiff : c.edges.countP p + 1 = c.edges.countP q :=
    List.countP_add_one_eq_of_eq_except c.edges target p q
      hc.isTrail.edges_nodup he hp hq heq
  have hqeven : Even (c.edges.countP q) := by
    rw [← walkCutCrossings_eq_countP_edges]
    exact even_walkCutCrossings_of_isClosed _ c
  rw [← hdiff] at hqeven
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hqeven)

/-- Away from the boundary, the row-ray sets of the two faces separated by a
vertical edge differ only by that edge.  If it is absent from the walk, the
sets are therefore equal. -/
theorem rowRayCrossingEdges_eq_across_internal_vertical_of_not_mem_edges
    {m n : Nat} {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (_hleft : e.col.val ≠ 0) (_hright : e.col.val + 1 ≠ n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    rowRayCrossingEdges c e.row ⟨e.col.val - 1, by omega⟩ =
      rowRayCrossingEdges c e.row ⟨e.col.val, by omega⟩ := by
  ext a
  simp only [mem_rowRayCrossingEdges_iff]
  constructor
  · rintro ⟨ha, har, hac⟩
    exact ⟨ha, har, by omega⟩
  · rintro ⟨ha, har, hac⟩
    refine ⟨ha, har, ?_⟩
    by_contra hnot
    have hcol : a.col.val = e.col.val := by omega
    have hae : a = e :=
      verticalGridEdge_eq_of_row_eq_of_col_val_eq har hcol
    subst a
    exact he ha

/-- Internal vertical non-cycle edges preserve row-ray parity. -/
theorem faceRowRayOdd_vertical_internal_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (hleft : e.col.val ≠ 0) (hright : e.col.val + 1 ≠ n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    FaceRowRayOdd c (verticalDualEndpoints e).1 ↔
      FaceRowRayOdd c (verticalDualEndpoints e).2 := by
  rw [show (verticalDualEndpoints e).1 =
      GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
        simp [verticalDualEndpoints, hleft]]
  rw [show (verticalDualEndpoints e).2 =
      GridFace.cell e.row ⟨e.col.val, by omega⟩ by
        simp [verticalDualEndpoints, hright]]
  simp only [FaceRowRayOdd]
  rw [rowRayCrossingEdges_eq_across_internal_vertical_of_not_mem_edges
    c e hleft hright he]

/-- At the left boundary, the first row-ray prefix contains only the boundary
vertical edge itself. -/
theorem rowRayCrossingEdges_left_eq_empty_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n) (hleft : e.col.val = 0)
    (hright : e.col.val + 1 ≠ n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    rowRayCrossingEdges c e.row ⟨0, by omega⟩ = ∅ := by
  ext a
  simp only [mem_rowRayCrossingEdges_iff, Finset.notMem_empty, iff_false]
  rintro ⟨ha, har, hac⟩
  have hcol : a.col.val = e.col.val := by omega
  have hae : a = e :=
    verticalGridEdge_eq_of_row_eq_of_col_val_eq har hcol
  subst a
  exact he ha

/-- A non-cycle vertical edge on the left boundary preserves row-ray parity. -/
theorem faceRowRayOdd_vertical_left_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n) (hleft : e.col.val = 0)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    FaceRowRayOdd c (verticalDualEndpoints e).1 ↔
      FaceRowRayOdd c (verticalDualEndpoints e).2 := by
  rw [show (verticalDualEndpoints e).1 = GridFace.out by
    simp [verticalDualEndpoints, hleft]]
  by_cases hright : e.col.val + 1 = n
  · rw [show (verticalDualEndpoints e).2 = GridFace.out by
      simp [verticalDualEndpoints, hright]]
  · rw [show (verticalDualEndpoints e).2 =
        GridFace.cell e.row ⟨0, by omega⟩ by
      simp only [verticalDualEndpoints, dif_neg hright]
      congr 2]
    simp only [FaceRowRayOdd, false_iff, Nat.not_odd_iff_even]
    rw [rowRayCrossingEdges_left_eq_empty_of_not_mem_edges c e hleft hright he]
    simp

/-- All vertical walk edges crossing one complete row boundary. -/
def rowCrossingEdges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (row : Fin (m - 1)) : Finset (VerticalGridEdge m n) :=
  Finset.univ.filter fun e =>
    s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges ∧ e.row = row

@[simp] theorem mem_rowCrossingEdges_iff {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (row : Fin (m - 1)) (e : VerticalGridEdge m n) :
    e ∈ rowCrossingEdges c row ↔
      s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2) ∈ c.edges ∧ e.row = row := by
  simp [rowCrossingEdges]

theorem even_rowCrossingEdges_card {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsTrail) (row : Fin (m - 1)) :
    Even (rowCrossingEdges c row).card := by
  let edgeOf : VerticalGridEdge m n → Sym2 (GridVertex m n) := fun a =>
    s((verticalPrimalEndpoints a).1, (verticalPrimalEndpoints a).2)
  have himage : (rowCrossingEdges c row).image edgeOf =
      hc.edgesFinset.filter (fun edge =>
        EdgeCrossesBoolCut (gridRowPrefixSide row) edge = true) := by
    ext edge
    simp only [Finset.mem_image, mem_rowCrossingEdges_iff,
      Finset.mem_filter, Finset.mem_mk, Multiset.mem_coe]
    constructor
    · rintro ⟨a, ⟨ha, har⟩, rfl⟩
      exact ⟨ha, (vertical_edge_crosses_gridRowPrefixSide_iff row a).mpr har⟩
    · rintro ⟨hedge, hcross⟩
      induction edge using Sym2.inductionOn with
      | _ x y =>
          have hadj := hG (c.adj_of_mem_edges hedge)
          rcases gridGraph_adj_exists_coordinate_edge hadj with h | h
          · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
            · have hfalse := horizontal_edge_not_crosses_gridRowPrefixSide row a
              change EdgeCrossesBoolCut (gridRowPrefixSide row)
                (Sym2.mk (horizontalPrimalEndpoints a)) = false at hfalse
              rw [hfalse] at hcross
              contradiction
            · rw [Sym2.eq_swap] at hcross ⊢
              have hfalse := horizontal_edge_not_crosses_gridRowPrefixSide row a
              change EdgeCrossesBoolCut (gridRowPrefixSide row)
                (Sym2.mk (horizontalPrimalEndpoints a)) = false at hfalse
              rw [hfalse] at hcross
              contradiction
          · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
            · refine ⟨a, ⟨hedge,
                (vertical_edge_crosses_gridRowPrefixSide_iff row a).mp hcross⟩, rfl⟩
            · rw [Sym2.eq_swap] at hcross ⊢
              refine ⟨a, ⟨?_,
                (vertical_edge_crosses_gridRowPrefixSide_iff row a).mp hcross⟩, rfl⟩
              simpa only [Sym2.eq_swap] using hedge
  have hcard : (rowCrossingEdges c row).card =
      c.edges.countP (EdgeCrossesBoolCut (gridRowPrefixSide row)) := by
    rw [← Finset.card_image_of_injective (rowCrossingEdges c row)
      verticalPrimalEndpoints_sym2_injective, himage,
      List.countP_eq_length_filter]
    have hfilter :
        (c.edges.filter (EdgeCrossesBoolCut (gridRowPrefixSide row))).toFinset =
          hc.edgesFinset.filter (fun edge =>
            EdgeCrossesBoolCut (gridRowPrefixSide row) edge = true) := by
      ext edge
      simp
    rw [← hfilter, List.toFinset_card_of_nodup
      (hc.edges_nodup.filter (EdgeCrossesBoolCut (gridRowPrefixSide row)))]
  rw [hcard, ← walkCutCrossings_eq_countP_edges]
  exact even_gridRowPrefix_crossings c row

theorem rowRayCrossingEdges_right_eq_insert_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (hleft : e.col.val ≠ 0) (hright : e.col.val + 1 ≠ n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges) :
    rowRayCrossingEdges c e.row ⟨e.col.val, by omega⟩ =
      insert e (rowRayCrossingEdges c e.row ⟨e.col.val - 1, by omega⟩) := by
  ext a
  simp only [mem_rowRayCrossingEdges_iff, Finset.mem_insert]
  constructor
  · rintro ⟨ha, har, hac⟩
    by_cases hcol : a.col.val = e.col.val
    · left
      exact verticalGridEdge_eq_of_row_eq_of_col_val_eq har hcol
    · right
      exact ⟨ha, har, by omega⟩
  · rintro (rfl | ⟨ha, har, hac⟩)
    · exact ⟨he, rfl, le_rfl⟩
    · exact ⟨ha, har, by omega⟩

theorem rowRayCrossingEdges_left_eq_singleton_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n) (hleft : e.col.val = 0)
    (hright : e.col.val + 1 ≠ n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges) :
    rowRayCrossingEdges c e.row ⟨0, by omega⟩ = {e} := by
  ext a
  simp only [mem_rowRayCrossingEdges_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨_, har, hac⟩
    apply verticalGridEdge_eq_of_row_eq_of_col_val_eq har
    omega
  · rintro rfl
    exact ⟨he, rfl, by omega⟩

theorem rowCrossingEdges_eq_insert_rightPrefix_of_right_boundary {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (hleft : e.col.val ≠ 0)
    (hright : e.col.val + 1 = n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges) :
    rowCrossingEdges c e.row =
      insert e (rowRayCrossingEdges c e.row ⟨e.col.val - 1, by omega⟩) := by
  ext a
  simp only [mem_rowCrossingEdges_iff, Finset.mem_insert,
    mem_rowRayCrossingEdges_iff]
  constructor
  · rintro ⟨ha, har⟩
    by_cases hcol : a.col.val = e.col.val
    · left
      exact verticalGridEdge_eq_of_row_eq_of_col_val_eq har hcol
    · right
      exact ⟨ha, har, by omega⟩
  · rintro (rfl | ⟨ha, har, _⟩)
    · exact ⟨he, rfl⟩
    · exact ⟨ha, har⟩

theorem rowCrossingEdges_eq_rightPrefix_of_right_boundary_not_mem {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w) (e : VerticalGridEdge m n)
    (hleft : e.col.val ≠ 0) (hright : e.col.val + 1 = n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    rowCrossingEdges c e.row =
      rowRayCrossingEdges c e.row ⟨e.col.val - 1, by omega⟩ := by
  ext a
  simp only [mem_rowCrossingEdges_iff, mem_rowRayCrossingEdges_iff]
  constructor
  · rintro ⟨ha, har⟩
    refine ⟨ha, har, ?_⟩
    by_contra hnot
    have hcol : a.col.val = e.col.val := by omega
    have hae := verticalGridEdge_eq_of_row_eq_of_col_val_eq har hcol
    subst a
    exact he ha
  · rintro ⟨ha, har, _⟩
    exact ⟨ha, har⟩

theorem faceRowRayOdd_vertical_right_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsTrail) (e : VerticalGridEdge m n)
    (hleft : e.col.val ≠ 0) (hright : e.col.val + 1 = n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∉ c.edges) :
    FaceRowRayOdd c (verticalDualEndpoints e).1 ↔
      FaceRowRayOdd c (verticalDualEndpoints e).2 := by
  rw [show (verticalDualEndpoints e).1 =
      GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
    simp [verticalDualEndpoints, hleft]]
  rw [show (verticalDualEndpoints e).2 = GridFace.out by
    simp [verticalDualEndpoints, hright]]
  simp only [FaceRowRayOdd, iff_false, Nat.not_odd_iff_even]
  rw [← rowCrossingEdges_eq_rightPrefix_of_right_boundary_not_mem
    c e hleft hright he]
  exact even_rowCrossingEdges_card hG c hc e.row

/-- At least one face incident to a vertical cycle edge has odd row-ray
parity. -/
theorem faceRowRayOdd_vertical_or_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : VerticalGridEdge m n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges) :
    FaceRowRayOdd c (verticalDualEndpoints e).1 ∨
      FaceRowRayOdd c (verticalDualEndpoints e).2 := by
  by_cases hleft : e.col.val = 0
  · by_cases hright : e.col.val + 1 = n
    · have hfull := even_rowCrossingEdges_card hG c hc.isTrail e.row
      have hsingleton : rowCrossingEdges c e.row = {e} := by
        ext a
        simp only [mem_rowCrossingEdges_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨_, har⟩
          apply verticalGridEdge_eq_of_row_eq_of_col_val_eq har
          omega
        · rintro rfl
          exact ⟨he, rfl⟩
      rw [hsingleton] at hfull
      simp at hfull
    · right
      have hn : 1 ≠ n := by omega
      rw [show (verticalDualEndpoints e).2 =
          GridFace.cell e.row ⟨0, by omega⟩ by
        simp [verticalDualEndpoints, hleft, hn]]
      simp only [FaceRowRayOdd]
      rw [rowRayCrossingEdges_left_eq_singleton_of_mem_edges
        c e hleft hright he]
      simp
  · by_cases hright : e.col.val + 1 = n
    · left
      rw [show (verticalDualEndpoints e).1 =
          GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
        simp [verticalDualEndpoints, hleft]]
      simp only [FaceRowRayOdd]
      have hfull := even_rowCrossingEdges_card hG c hc.isTrail e.row
      rw [rowCrossingEdges_eq_insert_rightPrefix_of_right_boundary c e hleft hright he,
        Finset.card_insert_of_notMem] at hfull
      · exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hfull)
      · simp only [mem_rowRayCrossingEdges_iff, not_and_or]
        right
        right
        omega

    · rw [show (verticalDualEndpoints e).1 =
          GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
        simp [verticalDualEndpoints, hleft]]
      rw [show (verticalDualEndpoints e).2 =
          GridFace.cell e.row ⟨e.col.val, by omega⟩ by
        simp [verticalDualEndpoints, hright]]
      simp only [FaceRowRayOdd]
      rw [rowRayCrossingEdges_right_eq_insert_of_mem_edges
        c e hleft hright he, Finset.card_insert_of_notMem]
      · by_cases hodd : Odd (rowRayCrossingEdges c e.row
            ⟨e.col.val - 1, by omega⟩).card
        · exact Or.inl hodd
        · exact Or.inr ((Nat.odd_add_one).mpr hodd)
      · simp only [mem_rowRayCrossingEdges_iff, not_and_or]
        right
        right
        omega

/-- The central row-ray arithmetic proposition. A simple grid cycle has an odd
bounded cell, and crossing any primal edge absent from the cycle preserves
parity of its two incident faces.

The horizontal clause is the vertex-crossing parity calculation; the vertical
clause is the prefix-count calculation.  Together these are the standard
orthogonal ray-crossing lemma, stated entirely over finite coordinate sets. -/
def GridCycleRowRayParity : Prop :=
  ∀ {m n : Nat} (U : Finset (GridVertex m n))
    {v : GridVertex m n}
    (c : (forcedEdgeGraph (gridGraph m n)
      (↑U : Set (GridVertex m n))ᶜ).Walk v v),
    c.IsCycle →
      (∃ f : GridFace m n, FaceRowRayOdd c f) ∧
      (∀ e : HorizontalGridEdge m n,
        s((horizontalPrimalEndpoints e).1,
          (horizontalPrimalEndpoints e).2) ∉ c.edges →
        (FaceRowRayOdd c (horizontalDualEndpoints e).1 ↔
          FaceRowRayOdd c (horizontalDualEndpoints e).2)) ∧
      (∀ e : VerticalGridEdge m n,
        s((verticalPrimalEndpoints e).1,
          (verticalPrimalEndpoints e).2) ∉ c.edges →
          (FaceRowRayOdd c (verticalDualEndpoints e).1 ↔
            FaceRowRayOdd c (verticalDualEndpoints e).2))

/-- The finite row-ray parity theorem for simple rectangular-grid cycles. -/
theorem gridCycleRowRayParity : GridCycleRowRayParity := by
  intro m n U v c hc
  have hodd : ∃ f : GridFace m n, FaceRowRayOdd c f := by
    cases hedges : c.edges with
    | nil =>
        have hlen := hc.three_le_length
        rw [← SimpleGraph.Walk.length_edges, hedges] at hlen
        simp at hlen
    | cons edge rest =>
        have hedge : edge ∈ c.edges := by rw [hedges]; simp
        induction edge using Sym2.inductionOn with
        | _ x y =>
            have hadj := (c.adj_of_mem_edges hedge).1
            rcases gridGraph_adj_exists_coordinate_edge hadj with h | h
            · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
              · rcases faceRowRayOdd_horizontal_or_of_mem_edges
                  (forcedEdgeGraph_le _ _) c hc e hedge with h | h
                · exact ⟨(horizontalDualEndpoints e).1, h⟩
                · exact ⟨(horizontalDualEndpoints e).2, h⟩
              · rw [Sym2.eq_swap] at hedge
                rcases faceRowRayOdd_horizontal_or_of_mem_edges
                  (forcedEdgeGraph_le _ _) c hc e hedge with h | h
                · exact ⟨(horizontalDualEndpoints e).1, h⟩
                · exact ⟨(horizontalDualEndpoints e).2, h⟩
            · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
              · rcases faceRowRayOdd_vertical_or_of_mem_edges
                  (forcedEdgeGraph_le _ _) c hc e hedge with h | h
                · exact ⟨(verticalDualEndpoints e).1, h⟩
                · exact ⟨(verticalDualEndpoints e).2, h⟩
              · rw [Sym2.eq_swap] at hedge
                rcases faceRowRayOdd_vertical_or_of_mem_edges
                  (forcedEdgeGraph_le _ _) c hc e hedge with h | h
                · exact ⟨(verticalDualEndpoints e).1, h⟩
                · exact ⟨(verticalDualEndpoints e).2, h⟩
  refine ⟨hodd, ?_, ?_⟩
  · intro e he
    exact faceRowRayOdd_horizontal_iff_of_not_mem_edges
      (forcedEdgeGraph_le _ _) c hc e he
  · intro e he
    by_cases hleft : e.col.val = 0
    · exact faceRowRayOdd_vertical_left_iff_of_not_mem_edges c e hleft he
    · by_cases hright : e.col.val + 1 = n
      · exact faceRowRayOdd_vertical_right_iff_of_not_mem_edges
          (forcedEdgeGraph_le _ _) c hc.isTrail e hleft hright he
      · exact faceRowRayOdd_vertical_internal_iff_of_not_mem_edges
          c e hleft hright he

/-- Every edge of `G` stays on one side of the vertex cut `S`. -/
def RespectsCut {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y : V⦄, G.Adj x y → (x ∈ S ↔ y ∈ S)

/-- A walk cannot cross a cut respected by every graph edge. -/
theorem reachable_mem_iff_of_respectsCut {V : Type*} {G : SimpleGraph V}
    {S : Set V} (hcut : RespectsCut G S) {x y : V} (hxy : G.Reachable x y) :
    x ∈ S ↔ y ∈ S := by
  rcases hxy with ⟨p⟩
  induction p with
  | nil => rfl
  | @cons x z y hxz p ih =>
      exact (hcut hxz).trans ih

/-- A connected graph cannot respect a cut with vertices on both sides. -/
theorem not_connected_of_respectsCut {V : Type*} {G : SimpleGraph V}
    {S : Set V} (hcut : RespectsCut G S) (hin : S.Nonempty)
    (hout : (Sᶜ).Nonempty) : ¬G.Connected := by
  intro hconn
  obtain ⟨x, hx⟩ := hin
  obtain ⟨y, hy⟩ := hout
  exact hy (reachable_mem_iff_of_respectsCut hcut (hconn x y) |>.mp hx)

set_option maxHeartbeats 800000 in
/-- A finite graph with an edge and even degree at every vertex contains a
cycle.  This is the graph-theoretic endpoint used after finite cell-boundary
cancellation. -/
theorem not_isAcyclic_of_edgeFinset_nonempty_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hedge : G.edgeFinset.Nonempty)
    (heven : ∀ v, Even (G.degree v)) : ¬G.IsAcyclic := by
  classical
  intro hacyclic
  obtain ⟨e, he⟩ := hedge
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      let C := G.connectedComponentMk x
      have htree : C.toSimpleGraph.IsTree :=
        hacyclic.isTree_connectedComponent C
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      have hnontrivial : Nontrivial C := by
        refine ⟨⟨x, by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
          ⟨y, ?_⟩, ?_⟩
        · exact C.mem_supp_of_adj_mem_supp
            SimpleGraph.ConnectedComponent.connectedComponentMk_mem hxy
        · intro h
          exact hxy.ne (congrArg Subtype.val h)
      letI : Nontrivial C := hnontrivial
      obtain ⟨v, hv⟩ := htree.exists_vert_degree_one_of_nontrivial
      have hsupp : G.neighborSet v.1 ⊆ C.supp := by
        intro w hw
        exact C.mem_supp_of_adj_mem_supp v.2 hw
      have hdegree : C.toSimpleGraph.degree v = G.degree v.1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          ← SimpleGraph.card_neighborFinset_eq_degree]
        apply Finset.card_bij (fun w _ => w.1)
        · intro w hw
          simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hw
        · intro a ha b hb hab
          exact Subtype.ext hab
        · intro w hw
          exact ⟨⟨w, hsupp (by simpa using hw)⟩, by
            simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hw, rfl⟩
      have := heven v.1
      rw [← hdegree, hv] at this
      exact Nat.not_even_one this

/-- The local horizontal and vertical clauses of the row-ray lemma make parity
an invariant of every walk in the cycle-complement dual graph. -/
theorem cycleComplementDualGraph_respects_faceRowRayOdd {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v w : GridVertex m n}
    (c : G.Walk v w)
    (hh : ∀ e : HorizontalGridEdge m n,
      s((horizontalPrimalEndpoints e).1,
        (horizontalPrimalEndpoints e).2) ∉ c.edges →
      (FaceRowRayOdd c (horizontalDualEndpoints e).1 ↔
        FaceRowRayOdd c (horizontalDualEndpoints e).2))
    (hv : ∀ e : VerticalGridEdge m n,
      s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2) ∉ c.edges →
      (FaceRowRayOdd c (verticalDualEndpoints e).1 ↔
        FaceRowRayOdd c (verticalDualEndpoints e).2)) :
    RespectsCut (cycleComplementDualGraph c) {f | FaceRowRayOdd c f} := by
  intro x y hxy
  rcases hxy.2 with h | h
  · obtain ⟨e, he, hends⟩ := h
    exact (hasDualEndpoints_iff hends (FaceRowRayOdd c)).mpr (hh e he)
  · obtain ⟨e, he, hends⟩ := h
    exact (hasDualEndpoints_iff hends (FaceRowRayOdd c)).mpr (hv e he)

/-- The finite row-ray parity lemma implies bounded-face enclosure: an odd
face cannot be reached from the parity-zero unbounded face without crossing a
cycle edge. -/
theorem gridCycleEnclosesBoundedFace_of_rowRayParity
    (hparity : GridCycleRowRayParity) : GridCycleEnclosesBoundedFace := by
  intro m n U v c hcycle
  obtain ⟨⟨f, hf⟩, hh, hv⟩ := hparity U c hcycle
  have hcut : RespectsCut (cycleComplementDualGraph c)
      {f | FaceRowRayOdd c f} :=
    cycleComplementDualGraph_respects_faceRowRayOdd c hh hv
  have hnreach : ¬(cycleComplementDualGraph c).Reachable GridFace.out f := by
    intro hreach
    exact faceRowRayOdd_out c
      ((reachable_mem_iff_of_respectsCut hcut hreach).mpr hf)
  exact ⟨f, (mem_cycleInteriorFaces_iff c f).mpr hnreach⟩

/-- Concrete finite-grid cycle-separation proposition.  A cycle made only of
edges not internal to `U` must enclose a nonempty set of bounded faces, while
the two faces across every U-U primal edge lie on the same side of that cut.

This finite intermediate statement mentions only grid coordinates, walks, and
membership in a finite set of cells. -/
def GridPrimalCycleFaceCut : Prop :=
  ∀ {m n : Nat} (U : Finset (GridVertex m n))
    {v : GridVertex m n}
    (c : (forcedEdgeGraph (gridGraph m n)
      (↑U : Set (GridVertex m n))ᶜ).Walk v v),
    c.IsCycle →
      ∃ S : Finset (GridFace m n),
        S.Nonempty ∧ GridFace.out ∉ S ∧
        (∀ e : HorizontalGridEdge m n,
          (horizontalPrimalEndpoints e).1 ∈ U →
          (horizontalPrimalEndpoints e).2 ∈ U →
          ((horizontalDualEndpoints e).1 ∈ S ↔
            (horizontalDualEndpoints e).2 ∈ S)) ∧
        (∀ e : VerticalGridEdge m n,
          (verticalPrimalEndpoints e).1 ∈ U →
          (verticalPrimalEndpoints e).2 ∈ U →
          ((verticalDualEndpoints e).1 ∈ S ↔
            (verticalDualEndpoints e).2 ∈ S))

/-- The unreachable-face construction reduces `GridPrimalCycleFaceCut` to the
single standard enclosure statement `GridCycleEnclosesBoundedFace`. -/
theorem gridPrimalCycleFaceCut_of_cycleEnclosesBoundedFace
    (hencloses : GridCycleEnclosesBoundedFace) : GridPrimalCycleFaceCut := by
  intro m n U v c hcycle
  refine ⟨cycleInteriorFaces c, hencloses U c hcycle,
    out_not_mem_cycleInteriorFaces c, ?_, ?_⟩
  · intro e he₁ he₂
    exact horizontal_mem_cycleInteriorFaces_iff_of_not_mem_edges c e
      (horizontal_not_mem_forcedCycle_edges U c e he₁ he₂)
  · intro e he₁ he₂
    exact vertical_mem_cycleInteriorFaces_iff_of_not_mem_edges c e
      (vertical_not_mem_forcedCycle_edges U c e he₁ he₂)

/-- Row-ray parity supplies the complete finite primal face cut. -/
theorem gridPrimalCycleFaceCut_of_rowRayParity
    (hparity : GridCycleRowRayParity) : GridPrimalCycleFaceCut :=
  gridPrimalCycleFaceCut_of_cycleEnclosesBoundedFace
    (gridCycleEnclosesBoundedFace_of_rowRayParity hparity)

/-- The edge conditions in `GridPrimalCycleFaceCut` say exactly what is needed:
the U-U dual graph cannot cross the resulting face cut. -/
theorem uuDualGraph_respectsCut {m n : Nat}
    (U : Finset (GridVertex m n)) (S : Finset (GridFace m n))
    (hh : ∀ e : HorizontalGridEdge m n,
      (horizontalPrimalEndpoints e).1 ∈ U →
      (horizontalPrimalEndpoints e).2 ∈ U →
      ((horizontalDualEndpoints e).1 ∈ S ↔
        (horizontalDualEndpoints e).2 ∈ S))
    (hv : ∀ e : VerticalGridEdge m n,
      (verticalPrimalEndpoints e).1 ∈ U →
      (verticalPrimalEndpoints e).2 ∈ U →
      ((verticalDualEndpoints e).1 ∈ S ↔
        (verticalDualEndpoints e).2 ∈ S)) :
    RespectsCut (uuDualGraph U) (↑S : Set (GridFace m n)) := by
  intro x y hxy
  rcases hxy.2 with h | h
  · obtain ⟨e, he₁, he₂, hends⟩ := h
    exact (hasDualEndpoints_iff hends (fun f => f ∈ S)).mpr (hh e he₁ he₂)
  · obtain ⟨e, he₁, he₂, hends⟩ := h
    exact (hasDualEndpoints_iff hends (fun f => f ∈ S)).mpr (hv e he₁ he₂)

/-- Primal/dual cycle-separation statement connecting executable dual
certificates to acyclicity of the forced graph. -/
def GridDualCycleSeparation : Prop :=
  ∀ {m n : Nat} (U : Finset (GridVertex m n)),
    (uuDualGraph U).Connected →
      (forcedEdgeGraph (gridGraph m n) (↑U : Set (GridVertex m n))ᶜ).IsAcyclic

/-- Finite grid cycle-face separation implies the desired primal/dual
acyclicity statement. -/
theorem gridDualCycleSeparation_of_primalCycleFaceCut
    (hface : GridPrimalCycleFaceCut) : GridDualCycleSeparation := by
  intro m n U hdual v c hcycle
  obtain ⟨S, hSne, hout, hh, hv⟩ := hface U c hcycle
  have hcut : RespectsCut (uuDualGraph U) (↑S : Set (GridFace m n)) :=
    uuDualGraph_respectsCut U S hh hv
  have hin : (↑S : Set (GridFace m n)).Nonempty := by
    simpa using hSne
  have houtside : ((↑S : Set (GridFace m n))ᶜ).Nonempty := by
    exact ⟨GridFace.out, by simpa using hout⟩
  exact (not_connected_of_respectsCut hcut hin houtside hdual).elim

/-- Direct composition of finite grid enclosure with the desired dual-cycle
separation theorem. -/
theorem gridDualCycleSeparation_of_cycleEnclosesBoundedFace
    (hencloses : GridCycleEnclosesBoundedFace) : GridDualCycleSeparation :=
  gridDualCycleSeparation_of_primalCycleFaceCut
    (gridPrimalCycleFaceCut_of_cycleEnclosesBoundedFace hencloses)

/-- Direct endpoint of the row-ray approach. -/
theorem gridDualCycleSeparation_of_rowRayParity
    (hparity : GridCycleRowRayParity) : GridDualCycleSeparation :=
  gridDualCycleSeparation_of_cycleEnclosesBoundedFace
    (gridCycleEnclosesBoundedFace_of_rowRayParity hparity)

/-- Unconditional primal/dual cycle separation for rectangular grids. -/
theorem gridDualCycleSeparation : GridDualCycleSeparation :=
  gridDualCycleSeparation_of_rowRayParity gridCycleRowRayParity

/-- Once grid cycle separation is proved, dual connectivity is exactly the
construction-side certificate needed by the induced-edge decycling reduction. -/
theorem isInducedEdgeDecyclingSet_of_uuDual_connected
    (hsep : GridDualCycleSeparation) {m n : Nat}
    (U : Finset (GridVertex m n)) (hdual : (uuDualGraph U).Connected) :
    IsInducedEdgeDecyclingSet (gridGraph m n) (↑U : Set (GridVertex m n)) := by
  exact hsep U hdual

/-- Conditional construction endpoint: a connected U-U dual yields a spanning
tree preserving every vertex outside `U`. -/
theorem exists_isTree_preserving_compl_of_uuDual_connected
    (hsep : GridDualCycleSeparation) {m n : Nat}
    (U : Finset (GridVertex m n)) (hdual : (uuDualGraph U).Connected)
    (hgrid : (gridGraph m n).Connected) :
    ∃ T : SimpleGraph (GridVertex m n), T ≤ gridGraph m n ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex m n⦄, v ∈ (↑U : Set (GridVertex m n))ᶜ →
        preservesIncidentEdges (gridGraph m n) T v := by
  exact exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic hgrid (hsep U hdual)

/-- A connected U-U dual unconditionally yields a spanning tree preserving
every grid vertex outside `U`. -/
theorem exists_isTree_preserving_compl_of_uuDual_connected_grid {m n : Nat}
    (U : Finset (GridVertex m n)) (hdual : (uuDualGraph U).Connected)
    (hgrid : (gridGraph m n).Connected) :
    ∃ T : SimpleGraph (GridVertex m n), T ≤ gridGraph m n ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex m n⦄, v ∈ (↑U : Set (GridVertex m n))ᶜ →
        preservesIncidentEdges (gridGraph m n) T v := by
  exact exists_isTree_preserving_compl_of_uuDual_connected
    gridDualCycleSeparation U hdual hgrid

end GridGraphs
