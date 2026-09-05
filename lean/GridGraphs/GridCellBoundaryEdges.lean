import GridGraphs.BareCombTransition
import GridGraphs.UniversalWaste

/-!
# Coordinate-labelled boundary edges of a grid cell

This module packages the four sides of a unit cell as distinct `GridEdge`
labels.  It records their primal and dual endpoints and the local tree-cotree
dichotomy used by cell arguments.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

/-- The four sides of a unit grid cell, in clockwise order. -/
inductive GridCellSide where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype

def GridCellSide.opposite : GridCellSide → GridCellSide
  | .top => .bottom
  | .right => .left
  | .bottom => .top
  | .left => .right

@[simp] theorem GridCellSide.opposite_opposite (side : GridCellSide) :
    side.opposite.opposite = side := by
  cases side <;> rfl

/-- The coordinate-labelled edge on one side of a unit grid cell. -/
def gridCellBoundaryEdge {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    GridCellSide → GridEdge m n
  | .top => .horizontal ⟨⟨r.val, by omega⟩, c⟩
  | .right => .vertical ⟨r, ⟨c.val + 1, by omega⟩⟩
  | .bottom => .horizontal ⟨⟨r.val + 1, by omega⟩, c⟩
  | .left => .vertical ⟨r, ⟨c.val, by omega⟩⟩

/-- The face across a cell side from the cell itself. -/
def gridCellAcrossFace {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    GridCellSide → GridFace m n
  | .top => (gridCellBoundaryEdge r c .top).dualEndpoints.1
  | .right => (gridCellBoundaryEdge r c .right).dualEndpoints.2
  | .bottom => (gridCellBoundaryEdge r c .bottom).dualEndpoints.2
  | .left => (gridCellBoundaryEdge r c .left).dualEndpoints.1

@[simp] theorem gridCellBoundaryEdge_primalEndpoints_top {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridCellBoundaryEdge r c .top).primalEndpoints =
      (cell00 r c, cell01 r c) := by
  simp [gridCellBoundaryEdge, GridEdge.primalEndpoints, horizontalPrimalEndpoints,
    cell00, cell01]

@[simp] theorem gridCellBoundaryEdge_primalEndpoints_right {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridCellBoundaryEdge r c .right).primalEndpoints =
      (cell01 r c, cell11 r c) := by
  simp [gridCellBoundaryEdge, GridEdge.primalEndpoints, verticalPrimalEndpoints,
    cell01, cell11]

@[simp] theorem gridCellBoundaryEdge_primalEndpoints_bottom {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridCellBoundaryEdge r c .bottom).primalEndpoints =
      (cell10 r c, cell11 r c) := by
  simp [gridCellBoundaryEdge, GridEdge.primalEndpoints, horizontalPrimalEndpoints,
    cell10, cell11]

@[simp] theorem gridCellBoundaryEdge_primalEndpoints_left {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridCellBoundaryEdge r c .left).primalEndpoints =
      (cell00 r c, cell10 r c) := by
  simp [gridCellBoundaryEdge, GridEdge.primalEndpoints, verticalPrimalEndpoints,
    cell00, cell10]

/-- Exact primal endpoints, with the canonical orientation of `GridEdge`. -/
theorem gridCellBoundaryEdge_primalEndpoints {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide) :
    (gridCellBoundaryEdge r c side).primalEndpoints = match side with
      | .top => (cell00 r c, cell01 r c)
      | .right => (cell01 r c, cell11 r c)
      | .bottom => (cell10 r c, cell11 r c)
      | .left => (cell00 r c, cell10 r c) := by
  cases side <;> simp

/-- The incident faces, ordered according to the orientation of `GridEdge`. -/
@[simp] theorem gridCellBoundaryEdge_dualEndpoints {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide) :
    (gridCellBoundaryEdge r c side).dualEndpoints = match side with
      | .top => (gridCellAcrossFace r c .top, .cell r c)
      | .right => (.cell r c, gridCellAcrossFace r c .right)
      | .bottom => (.cell r c, gridCellAcrossFace r c .bottom)
      | .left => (gridCellAcrossFace r c .left, .cell r c) := by
  have hr := r.isLt
  have hc := c.isLt
  cases side <;>
    simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
      horizontalDualEndpoints, verticalDualEndpoints] <;> omega

@[simp] theorem gridCellAcrossFace_ne_cell {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide) :
    gridCellAcrossFace r c side ≠ GridFace.cell r c := by
  have hr := r.isLt
  have hc := c.isLt
  cases side with
  | top =>
      by_cases h : r.val = 0
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          horizontalDualEndpoints, h]
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          horizontalDualEndpoints, h, Fin.ext_iff]
        omega
  | right =>
      by_cases h : c.val + 2 = n
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          verticalDualEndpoints, h]
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          verticalDualEndpoints, h, Fin.ext_iff]
  | bottom =>
      by_cases h : r.val + 2 = m
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          horizontalDualEndpoints, h]
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          horizontalDualEndpoints, h, Fin.ext_iff]
  | left =>
      by_cases h : c.val = 0
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          verticalDualEndpoints, h]
      · simp [gridCellAcrossFace, gridCellBoundaryEdge, GridEdge.dualEndpoints,
          verticalDualEndpoints, h, Fin.ext_iff]
        omega

theorem gridCellBoundaryEdge_injective {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    Function.Injective (gridCellBoundaryEdge r c) := by
  intro a b h
  cases a <;> cases b <;> simp_all [gridCellBoundaryEdge]

private theorem acyclic_grid_cell_missing_fourth_side
    {m n : Nat} {T : SimpleGraph (GridVertex m n)}
    (hacyclic : T.IsAcyclic) (r : Fin (m - 1)) (c : Fin (n - 1))
    (htop : T.Adj (cell00 r c) (cell01 r c))
    (hright : T.Adj (cell01 r c) (cell11 r c))
    (hbottom : T.Adj (cell11 r c) (cell10 r c)) :
    ¬T.Adj (cell10 r c) (cell00 r c) := by
  intro hleft
  let q : T.Walk (cell01 r c) (cell00 r c) :=
    SimpleGraph.Walk.cons hright
      (SimpleGraph.Walk.cons hbottom
        (SimpleGraph.Walk.cons hleft SimpleGraph.Walk.nil))
  let p : T.Walk (cell00 r c) (cell00 r c) :=
    SimpleGraph.Walk.cons htop q
  have h00_01 := T.ne_of_adj htop
  have h01_11 := T.ne_of_adj hright
  have h11_10 := T.ne_of_adj hbottom
  have h10_00 := T.ne_of_adj hleft
  have hq_path : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      constructor
      · exact SimpleGraph.Walk.IsPath.of_adj hleft
      · simp [h11_10, (cell00_ne_cell11 r c).symm]
    · simp [h01_11, cell01_ne_cell10 r c, h00_01.symm]
  have hq_no_top : s(cell00 r c, cell01 r c) ∉ q.edges := by
    simp [q, h00_01, h01_11, h10_00.symm,
      cell00_ne_cell11 r c, cell01_ne_cell10 r c]
  apply hacyclic p
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  exact ⟨hq_path, hq_no_top⟩

/-- The four coordinate-labelled edges bounding a unit cell. -/
def gridCellBoundaryEdges {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    Finset (GridEdge m n) :=
  Finset.univ.image (gridCellBoundaryEdge r c)

@[simp] theorem mem_gridCellBoundaryEdges_iff {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) (e : GridEdge m n) :
    e ∈ gridCellBoundaryEdges r c ↔
      ∃ side : GridCellSide, gridCellBoundaryEdge r c side = e := by
  simp [gridCellBoundaryEdges]

@[simp] theorem card_gridCellBoundaryEdges {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridCellBoundaryEdges r c).card = 4 := by
  rw [gridCellBoundaryEdges, Finset.card_image_of_injective _
    (gridCellBoundaryEdge_injective r c)]
  decide

/-- A cell side belongs to the cotree exactly when `T` omits its endpoints. -/
theorem gridCellBoundaryEdge_mem_cotree_iff {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide) :
    (gridCellBoundaryEdge r c side).primalSym2 ∈
        (gridGraph m n \ T).edgeFinset ↔
      ¬T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
        (gridCellBoundaryEdge r c side).primalEndpoints.2 := by
  rw [SimpleGraph.mem_edgeFinset]
  exact and_iff_right (GridEdge.primalSym2_mem_gridGraph_edgeSet
    (gridCellBoundaryEdge r c side))

/-- If the two endpoints of one cell side preserve every incident grid edge,
the three sides touching those endpoints are retained. Tree acyclicity therefore
forces the opposite side to be omitted. -/
theorem gridCellBoundaryEdge_opposite_mem_cotree_of_preserved_side
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hfirst : preservesIncidentEdges (gridGraph m n) T
      (gridCellBoundaryEdge r c side).primalEndpoints.1)
    (hsecond : preservesIncidentEdges (gridGraph m n) T
      (gridCellBoundaryEdge r c side).primalEndpoints.2) :
    (gridCellBoundaryEdge r c side.opposite).primalSym2 ∈
      (gridGraph m n \ T).edgeFinset := by
  rw [gridCellBoundaryEdge_mem_cotree_iff]
  cases side with
  | top =>
      simp only [GridCellSide.opposite,
        gridCellBoundaryEdge_primalEndpoints_top,
        gridCellBoundaryEdge_primalEndpoints_bottom] at hfirst hsecond ⊢
      intro hbottom
      exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c
        (hfirst (gridGraph_cell_adj_top r c))
        (hsecond (gridGraph_cell_adj_right r c)) hbottom.symm
        (T.symm (hfirst (gridGraph_cell_adj_left r c).symm))
  | right =>
      simp only [GridCellSide.opposite,
        gridCellBoundaryEdge_primalEndpoints_right,
        gridCellBoundaryEdge_primalEndpoints_left] at hfirst hsecond ⊢
      intro hleft
      exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c
        (T.symm (hfirst (gridGraph_cell_adj_top r c).symm))
        (hfirst (gridGraph_cell_adj_right r c))
        (hsecond (gridGraph_cell_adj_bot r c)) hleft.symm
  | bottom =>
      simp only [GridCellSide.opposite,
        gridCellBoundaryEdge_primalEndpoints_bottom,
        gridCellBoundaryEdge_primalEndpoints_top] at hfirst hsecond ⊢
      intro htop
      exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c htop
        (T.symm (hsecond (gridGraph_cell_adj_right r c).symm))
        (T.symm (hfirst (gridGraph_cell_adj_bot r c).symm))
        (hfirst (gridGraph_cell_adj_left r c))
  | left =>
      simp only [GridCellSide.opposite,
        gridCellBoundaryEdge_primalEndpoints_left,
        gridCellBoundaryEdge_primalEndpoints_right] at hfirst hsecond ⊢
      intro hright
      exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c
        (hfirst (gridGraph_cell_adj_top r c)) hright
        (T.symm (hsecond (gridGraph_cell_adj_bot r c).symm))
        (T.symm (hfirst (gridGraph_cell_adj_left r c).symm))

/-- Subtype-packaged positive ordinary-gap theorem. The endpoint identities are
the explicit row/column formulas in `gridCellBoundaryEdge_primalEndpoints`. -/
def gridCellOppositeLabelledCotreeTransitionOfPreservedSide
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hfirst : preservesIncidentEdges (gridGraph m n) T
      (gridCellBoundaryEdge r c side).primalEndpoints.1)
    (hsecond : preservesIncidentEdges (gridGraph m n) T
      (gridCellBoundaryEdge r c side).primalEndpoints.2) :
    LabelledCotreeTransition T :=
  ⟨gridCellBoundaryEdge r c side.opposite,
    gridCellBoundaryEdge_opposite_mem_cotree_of_preserved_side
      hT r c side hfirst hsecond⟩

/-- With the southwest two adjacent cell sides retained, acyclicity forces at
least one of the northeast two sides into the cotree. Prefer the top side. -/
noncomputable def gridCellTopElseRightCotreeTransitionOfBottomLeftRetained
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1))
    (hbottom : T.Adj (cell11 r c) (cell10 r c))
    (hleft : T.Adj (cell10 r c) (cell00 r c)) :
    LabelledCotreeTransition T := by
  classical
  by_cases htop : T.Adj (cell00 r c) (cell01 r c)
  · refine ⟨gridCellBoundaryEdge r c .right, ?_⟩
    rw [gridCellBoundaryEdge_mem_cotree_iff]
    intro hright
    exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c htop hright
      hbottom hleft
  · exact ⟨gridCellBoundaryEdge r c .top,
      (gridCellBoundaryEdge_mem_cotree_iff T r c .top).2 htop⟩

/-- With the northeast two adjacent cell sides retained, acyclicity forces at
least one of the southwest two sides into the cotree. Prefer the bottom side. -/
noncomputable def gridCellBottomElseLeftCotreeTransitionOfTopRightRetained
    {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1))
    (htop : T.Adj (cell00 r c) (cell01 r c))
    (hright : T.Adj (cell01 r c) (cell11 r c)) :
    LabelledCotreeTransition T := by
  classical
  by_cases hbottom : T.Adj (cell11 r c) (cell10 r c)
  · refine ⟨gridCellBoundaryEdge r c .left, ?_⟩
    rw [gridCellBoundaryEdge_mem_cotree_iff]
    intro hleft
    exact acyclic_grid_cell_missing_fourth_side hT.isAcyclic r c htop hright
      hbottom (by
        simpa only [gridCellBoundaryEdge_primalEndpoints_left, adj_comm] using hleft)
  · exact ⟨gridCellBoundaryEdge r c .bottom,
      (gridCellBoundaryEdge_mem_cotree_iff T r c .bottom).2 (by
        simpa only [gridCellBoundaryEdge_primalEndpoints_bottom, adj_comm] using hbottom)⟩

/-- Both primal endpoints of a cotree cell side lie in cotree support. -/
theorem gridCellBoundaryEdge_endpoints_mem_cotree_support {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (h : (gridCellBoundaryEdge r c side).primalSym2 ∈
      (gridGraph m n \ T).edgeFinset) :
    (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
        supportFinset (gridGraph m n \ T) ∧
      (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
        supportFinset (gridGraph m n \ T) := by
  rw [SimpleGraph.mem_edgeFinset] at h
  constructor <;> rw [mem_supportFinset, SimpleGraph.degree_pos_iff_exists_adj]
  · exact ⟨_, h⟩
  · exact ⟨_, h.symm⟩

/-- A cotree side crosses a U-U dual edge when `U` is cotree support. -/
theorem gridCellBoundaryEdge_uuDualGraph_adj_of_mem_cotree {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (h : (gridCellBoundaryEdge r c side).primalSym2 ∈
      (gridGraph m n \ T).edgeFinset) :
    (uuDualGraph (supportFinset (gridGraph m n \ T))).Adj
      (GridFace.cell r c) (gridCellAcrossFace r c side) := by
  have hs := gridCellBoundaryEdge_endpoints_mem_cotree_support T r c side h
  refine ⟨(gridCellAcrossFace_ne_cell r c side).symm, ?_⟩
  cases side with
  | top =>
      left
      refine ⟨_, hs.1, hs.2, ?_⟩
      change HasDualEndpoints (gridCellBoundaryEdge r c .top).dualEndpoints
        (GridFace.cell r c) (gridCellAcrossFace r c .top)
      rw [gridCellBoundaryEdge_dualEndpoints]
      exact Or.inr ⟨rfl, rfl⟩
  | right =>
      right
      refine ⟨_, hs.1, hs.2, ?_⟩
      change HasDualEndpoints (gridCellBoundaryEdge r c .right).dualEndpoints
        (GridFace.cell r c) (gridCellAcrossFace r c .right)
      rw [gridCellBoundaryEdge_dualEndpoints]
      exact Or.inl ⟨rfl, rfl⟩
  | bottom =>
      left
      refine ⟨_, hs.1, hs.2, ?_⟩
      change HasDualEndpoints (gridCellBoundaryEdge r c .bottom).dualEndpoints
        (GridFace.cell r c) (gridCellAcrossFace r c .bottom)
      rw [gridCellBoundaryEdge_dualEndpoints]
      exact Or.inl ⟨rfl, rfl⟩
  | left =>
      right
      refine ⟨_, hs.1, hs.2, ?_⟩
      change HasDualEndpoints (gridCellBoundaryEdge r c .left).dualEndpoints
        (GridFace.cell r c) (gridCellAcrossFace r c .left)
      rw [gridCellBoundaryEdge_dualEndpoints]
      exact Or.inr ⟨rfl, rfl⟩

/-- A retained side whose endpoints have positive cotree degree is an internal
cotree-support resource. -/
theorem gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_pos {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hT : T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
      (gridCellBoundaryEdge r c side).primalEndpoints.2)
    (h₁ : 0 < (gridGraph m n \ T).degree
      (gridCellBoundaryEdge r c side).primalEndpoints.1)
    (h₂ : 0 < (gridGraph m n \ T).degree
      (gridCellBoundaryEdge r c side).primalEndpoints.2) :
    (gridCellBoundaryEdge r c side).primalSym2 ∈
      internalEdgeFinset T (supportFinset (gridGraph m n \ T)) := by
  rw [mem_internalEdgeFinset]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.mem_edgeFinset]
    exact hT
  · intro v hv
    rw [GridEdge.primalSym2, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact mem_supportFinset.mpr h₁
    · exact mem_supportFinset.mpr h₂

/-- Support-membership form of the retained-side internal-resource lemma. -/
theorem gridCellBoundaryEdge_mem_internalEdgeFinset_of_supported {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hT : T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
      (gridCellBoundaryEdge r c side).primalEndpoints.2)
    (h₁ : (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
      supportFinset (gridGraph m n \ T))
    (h₂ : (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
      supportFinset (gridGraph m n \ T)) :
    (gridCellBoundaryEdge r c side).primalSym2 ∈
      internalEdgeFinset T (supportFinset (gridGraph m n \ T)) := by
  apply gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_pos T r c side hT
  · exact mem_supportFinset.mp h₁
  · exact mem_supportFinset.mp h₂

/-- Strict tree-degree deficiency at both endpoints supplies the cotree support
needed by a retained cell side. -/
theorem gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_lt {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTG : T ≤ gridGraph m n)
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hT : T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
      (gridCellBoundaryEdge r c side).primalEndpoints.2)
    (h₁ : T.degree (gridCellBoundaryEdge r c side).primalEndpoints.1 <
      (gridGraph m n).degree
        (gridCellBoundaryEdge r c side).primalEndpoints.1)
    (h₂ : T.degree (gridCellBoundaryEdge r c side).primalEndpoints.2 <
      (gridGraph m n).degree
        (gridCellBoundaryEdge r c side).primalEndpoints.2) :
    (gridCellBoundaryEdge r c side).primalSym2 ∈
      internalEdgeFinset T (supportFinset (gridGraph m n \ T)) := by
  apply gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_pos T r c side hT
  · rw [degree_sdiff_of_le (gridGraph m n) T hTG]
    omega
  · rw [degree_sdiff_of_le (gridGraph m n) T hTG]
    omega

/-- In particular, a retained side between two ambient degree-four vertices of
tree degree three is an internal cotree-support resource. -/
theorem gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_three {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hTG : T ≤ gridGraph m n)
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (hT : T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
      (gridCellBoundaryEdge r c side).primalEndpoints.2)
    (hgrid₁ : (gridGraph m n).degree
      (gridCellBoundaryEdge r c side).primalEndpoints.1 = 4)
    (hgrid₂ : (gridGraph m n).degree
      (gridCellBoundaryEdge r c side).primalEndpoints.2 = 4)
    (hT₁ : T.degree
      (gridCellBoundaryEdge r c side).primalEndpoints.1 = 3)
    (hT₂ : T.degree
      (gridCellBoundaryEdge r c side).primalEndpoints.2 = 3) :
    (gridCellBoundaryEdge r c side).primalSym2 ∈
      internalEdgeFinset T (supportFinset (gridGraph m n \ T)) := by
  apply gridCellBoundaryEdge_mem_internalEdgeFinset_of_degree_lt T hTG r c side hT
  · omega
  · omega

/-- A supported cell side is either a retained internal resource or its exact
coordinate label is a cotree transition. -/
theorem gridCellBoundaryEdge_internal_or_labelledCotree {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (h₁ : (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
      supportFinset (gridGraph m n \ T))
    (h₂ : (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
      supportFinset (gridGraph m n \ T)) :
    (∃ e : ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))),
        e.1 = (gridCellBoundaryEdge r c side).primalSym2) ∨
      (∃ e : LabelledCotreeTransition T,
        e.1 = gridCellBoundaryEdge r c side) := by
  classical
  by_cases hT : T.Adj (gridCellBoundaryEdge r c side).primalEndpoints.1
      (gridCellBoundaryEdge r c side).primalEndpoints.2
  · exact Or.inl ⟨⟨_, gridCellBoundaryEdge_mem_internalEdgeFinset_of_supported
      T r c side hT h₁ h₂⟩, rfl⟩
  · exact Or.inr ⟨⟨_, (gridCellBoundaryEdge_mem_cotree_iff T r c side).2 hT⟩, rfl⟩

/-- Raw local resource carried by a supported cell side.  Retained sides use
the internal support edge; omitted sides keep their exact coordinate-labelled
cotree occurrence so that a later component/exposure layer can replace it by
the raw free component with its first-owner witness. -/
abbrev GridCellSupportedSideRawResource {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  ↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
    LabelledCotreeTransition T

noncomputable def gridCellSupportedSideRawResource {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (h₁ : (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
      supportFinset (gridGraph m n \ T))
    (h₂ : (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
      supportFinset (gridGraph m n \ T)) :
    GridCellSupportedSideRawResource T :=
  Classical.choose (show ∃ z : GridCellSupportedSideRawResource T,
      match z with
      | .inl e => e.1 = (gridCellBoundaryEdge r c side).primalSym2
      | .inr e => e.1 = gridCellBoundaryEdge r c side by
    rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c side h₁ h₂ with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact ⟨.inl e, he⟩
    · exact ⟨.inr e, he⟩)

/-- The selected local resource always retains the exact boundary-side label.
This is the local per-cell collision invariant; any later collision can only
come from forgetting an omitted edge to a raw free component. -/
theorem gridCellSupportedSideRawResource_label {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) (side : GridCellSide)
    (h₁ : (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
      supportFinset (gridGraph m n \ T))
    (h₂ : (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
      supportFinset (gridGraph m n \ T)) :
    match gridCellSupportedSideRawResource T r c side h₁ h₂ with
    | .inl e => e.1 = (gridCellBoundaryEdge r c side).primalSym2
    | .inr e => e.1 = gridCellBoundaryEdge r c side :=
  Classical.choose_spec (show ∃ z : GridCellSupportedSideRawResource T,
      match z with
      | .inl e => e.1 = (gridCellBoundaryEdge r c side).primalSym2
      | .inr e => e.1 = gridCellBoundaryEdge r c side by
    rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c side h₁ h₂ with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact ⟨.inl e, he⟩
    · exact ⟨.inr e, he⟩)

/-- Every cell of a grid spanning tree supplies either an internal supported
tree edge or an exact labelled cotree transition on one of its four sides. -/
theorem gridTreeCell_internal_or_labelledCotree {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (∃ side : GridCellSide,
      ∃ e : ↥(internalEdgeFinset T
        (supportFinset (gridGraph m n \ T))),
        e.1 = (gridCellBoundaryEdge r c side).primalSym2) ∨
    (∃ side : GridCellSide, ∃ e : LabelledCotreeTransition T,
      e.1 = gridCellBoundaryEdge r c side) := by
  classical
  rcases grid_tree_cotree_support_hits_cell_edge hT r c with
    h | h | h | h
  · rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c .top h.1 h.2 with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl ⟨.top, e, he⟩
    · exact Or.inr ⟨.top, e, he⟩
  · rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c .right h.1 h.2 with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl ⟨.right, e, he⟩
    · exact Or.inr ⟨.right, e, he⟩
  · rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c .bottom h.2 h.1 with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl ⟨.bottom, e, he⟩
    · exact Or.inr ⟨.bottom, e, he⟩
  · rcases gridCellBoundaryEdge_internal_or_labelledCotree T r c .left h.2 h.1 with
      ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl ⟨.left, e, he⟩
    · exact Or.inr ⟨.left, e, he⟩

/-- A spanning-tree cell supplies one concrete supported side.  Keeping the
side and its endpoint proofs together allows later hull walks to inspect the
exact local resource without choosing from an unproved resource subtype. -/
structure GridTreeCellSupportedSide {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (r : Fin (m - 1)) (c : Fin (n - 1)) where
  side : GridCellSide
  first_supported : (gridCellBoundaryEdge r c side).primalEndpoints.1 ∈
    supportFinset (gridGraph m n \ T)
  second_supported : (gridCellBoundaryEdge r c side).primalEndpoints.2 ∈
    supportFinset (gridGraph m n \ T)

/-- Canonical supported side selected from the unconditional cell-support
lemma for a grid spanning tree. -/
noncomputable def gridTreeCellSupportedSide {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    GridTreeCellSupportedSide T r c :=
  Classical.choose (show ∃ side : GridTreeCellSupportedSide T r c, True by
    rcases grid_tree_cotree_support_hits_cell_edge hT r c with h | h | h | h
    · exact ⟨⟨.top, h.1, h.2⟩, trivial⟩
    · exact ⟨⟨.right, h.1, h.2⟩, trivial⟩
    · exact ⟨⟨.bottom, by simpa using h.2, by simpa using h.1⟩, trivial⟩
    · exact ⟨⟨.left, by simpa using h.2, by simpa using h.1⟩, trivial⟩)

/-- Raw internal-edge/cotree-continuation resource on the selected supported
side of a cell. -/
noncomputable def gridTreeCellSupportedSideRawResource {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    GridCellSupportedSideRawResource T :=
  let side := gridTreeCellSupportedSide T hT r c
  gridCellSupportedSideRawResource T r c side.side
    side.first_supported side.second_supported

end GridGraphs
