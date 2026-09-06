import GridGraphs.Surgery.GridCrop
import GridGraphs.Geometry.GridBoundaryCycle
import GridGraphs.Geometry.GridEdge
import GridGraphs.Geometry.StraightForcedComponents

/-!
# Components and frame incidences of a grid crop

This file relates the forced components in a contiguous crop to the ambient
forced components.  It also records the physical grid edges which leave the
crop, without forgetting either their position on the crop boundary or their
ambient coordinate edge.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- A coordinate offset, packaged as an induced graph embedding. -/
def gridOffsetGraphEmbedding {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n) :
    gridGraph p q ↪g gridGraph m n where
  toEmbedding := gridOffsetEmbedding rowOffset colOffset hrows hcols
  map_rel_iff' := by
    intro v w
    exact gridOffsetEmbedding_adj_iff rowOffset colOffset hrows hcols v w

@[simp] theorem gridOffsetGraphEmbedding_apply {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (v : GridVertex p q) :
    gridOffsetGraphEmbedding rowOffset colOffset hrows hcols v =
      gridOffsetEmbedding rowOffset colOffset hrows hcols v := by rfl

/-- Exact coordinate description of the vertices retained by an offset crop. -/
theorem mem_range_gridOffsetEmbedding_iff {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (v : GridVertex m n) :
    v ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) ↔
      rowOffset ≤ v.1.val ∧ v.1.val < rowOffset + p ∧
        colOffset ≤ v.2.val ∧ v.2.val < colOffset + q := by
  constructor
  · rintro ⟨w, rfl⟩
    simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val]
    omega
  · rintro ⟨hr₀, hr₁, hc₀, hc₁⟩
    let w : GridVertex p q :=
      (⟨v.1.val - rowOffset, by omega⟩, ⟨v.2.val - colOffset, by omega⟩)
    refine ⟨w, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;>
      simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val, w] <;> omega

/-- The graph induced by the forced vertices retained by a crop. -/
abbrev cropInducedForcedGraph {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (F : Set (GridVertex m n)) :=
  (gridGraph p q).induce
    ((gridOffsetEmbedding rowOffset colOffset hrows hcols) ⁻¹' F)

/-- Inclusion of the crop's induced forced graph into the ambient induced
forced graph. -/
def cropInducedForcedToAmbientHom {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (F : Set (GridVertex m n)) :
    cropInducedForcedGraph rowOffset colOffset hrows hcols F →g
      (gridGraph m n).induce F where
  toFun v := ⟨gridOffsetEmbedding rowOffset colOffset hrows hcols v.1, v.2⟩
  map_rel' := by
    intro v w hvw
    exact (gridOffsetEmbedding_adj_iff rowOffset colOffset hrows hcols v.1 w.1).2 hvw

@[simp] theorem cropInducedForcedToAmbientHom_val {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (F : Set (GridVertex m n))
    (v : (gridOffsetEmbedding rowOffset colOffset hrows hcols) ⁻¹' F) :
    (cropInducedForcedToAmbientHom rowOffset colOffset hrows hcols F v).1 =
      gridOffsetEmbedding rowOffset colOffset hrows hcols v.1 := rfl

/-- The ambient forced component containing a component of the crop. -/
def cropConnectedComponentAncestor {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (F : Set (GridVertex m n))
    (C : (cropInducedForcedGraph rowOffset colOffset hrows hcols F).ConnectedComponent) :
    ((gridGraph m n).induce F).ConnectedComponent :=
  C.map (cropInducedForcedToAmbientHom rowOffset colOffset hrows hcols F)

@[simp] theorem cropConnectedComponentAncestor_mk {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (F : Set (GridVertex m n))
    (v : (gridOffsetEmbedding rowOffset colOffset hrows hcols) ⁻¹' F) :
    cropConnectedComponentAncestor rowOffset colOffset hrows hcols F
        ((cropInducedForcedGraph rowOffset colOffset hrows hcols F).connectedComponentMk v) =
      ((gridGraph m n).induce F).connectedComponentMk
        ⟨gridOffsetEmbedding rowOffset colOffset hrows hcols v.1, v.2⟩ := rfl

/-- Induced forced graph in a total-three square crop. -/
abbrev threeSideCropInducedForcedGraph
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n)) :=
  (gridGraph (n - 3) (n - 3)).induce
    ((threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F)

/-- Inclusion of a total-three crop's induced forced graph into the ambient
induced forced graph. -/
def threeSideCropInducedForcedToAmbientHom
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n)) :
    threeSideCropInducedForcedGraph n top bottom left right hn hrows hcols F →g
      (gridGraph n n).induce F where
  toFun v :=
    ⟨threeSideCropEmbedding n top bottom left right hn hrows hcols v.1, v.2⟩
  map_rel' := by
    intro v w hvw
    exact (threeSideCropEmbedding_adj_iff n top bottom left right hn hrows hcols
      v.1 w.1).2 hvw

/-- Ambient ancestor of a component in a total-three square crop. -/
def threeSideCropConnectedComponentAncestor
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (C : (threeSideCropInducedForcedGraph n top bottom left right hn hrows hcols F).ConnectedComponent) :
    ((gridGraph n n).induce F).ConnectedComponent :=
  C.map (threeSideCropInducedForcedToAmbientHom
    n top bottom left right hn hrows hcols F)

@[simp] theorem threeSideCropConnectedComponentAncestor_mk
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (v : (threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F) :
    threeSideCropConnectedComponentAncestor n top bottom left right hn hrows hcols F
        ((threeSideCropInducedForcedGraph n top bottom left right hn hrows hcols F).connectedComponentMk v) =
      ((gridGraph n n).induce F).connectedComponentMk
        ⟨threeSideCropEmbedding n top bottom left right hn hrows hcols v.1, v.2⟩ := rfl

/-- The two possible axes of a straight induced forced component. -/
inductive ForcedComponentAxis
  | horizontal
  | vertical
  deriving DecidableEq

instance : Fintype ForcedComponentAxis where
  elems := {.horizontal, .vertical}
  complete := by intro axis; cases axis <;> simp

/-- Axes on which all vertices of an induced forced component have a constant
coordinate.  A singleton component validly has both axes. -/
noncomputable def inducedForcedComponentValidAxes {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    Finset ForcedComponentAxis := by
  classical
  exact Finset.univ.filter fun axis =>
    match axis with
    | .horizontal => ∃ r : Fin m, ∀ v ∈ C.supp, v.1.1 = r
    | .vertical => ∃ c : Fin n, ∀ v ∈ C.supp, v.1.2 = c

@[simp] theorem horizontal_mem_inducedForcedComponentValidAxes_iff
    {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    .horizontal ∈ inducedForcedComponentValidAxes C ↔
      ∃ r : Fin m, ∀ v ∈ C.supp, v.1.1 = r := by
  simp [inducedForcedComponentValidAxes]

@[simp] theorem vertical_mem_inducedForcedComponentValidAxes_iff
    {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    .vertical ∈ inducedForcedComponentValidAxes C ↔
      ∃ c : Fin n, ∀ v ∈ C.supp, v.1.2 = c := by
  simp [inducedForcedComponentValidAxes]

/-- Prefer the horizontal tag when both axes are valid, and return no tag only
when the component has no valid straight axis. -/
noncomputable def inducedForcedComponentTag? {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    Option ForcedComponentAxis :=
  if .horizontal ∈ inducedForcedComponentValidAxes C then some .horizontal
  else if .vertical ∈ inducedForcedComponentValidAxes C then some .vertical
  else none

@[simp] theorem inducedForcedComponentTag?_eq_some_horizontal_iff
    {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    inducedForcedComponentTag? C = some .horizontal ↔
      .horizontal ∈ inducedForcedComponentValidAxes C := by
  by_cases h : .horizontal ∈ inducedForcedComponentValidAxes C <;>
    simp [inducedForcedComponentTag?, h]

@[simp] theorem inducedForcedComponentTag?_eq_some_vertical_iff
    {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    inducedForcedComponentTag? C = some .vertical ↔
      .horizontal ∉ inducedForcedComponentValidAxes C ∧
        .vertical ∈ inducedForcedComponentValidAxes C := by
  by_cases hh : .horizontal ∈ inducedForcedComponentValidAxes C
  · simp [inducedForcedComponentTag?, hh]
  · by_cases hv : .vertical ∈ inducedForcedComponentValidAxes C <;>
      simp [inducedForcedComponentTag?, hh, hv]

@[simp] theorem inducedForcedComponentTag?_eq_none_iff
    {m n : Nat} {F : Set (GridVertex m n)}
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    inducedForcedComponentTag? C = none ↔
      inducedForcedComponentValidAxes C = ∅ := by
  by_cases hh : .horizontal ∈ inducedForcedComponentValidAxes C
  · constructor
    · simp [inducedForcedComponentTag?, hh]
    · intro hempty
      rw [hempty] at hh
      simp at hh
  · by_cases hv : .vertical ∈ inducedForcedComponentValidAxes C
    · constructor
      · simp [inducedForcedComponentTag?, hh, hv]
      · intro hempty
        rw [hempty] at hv
        simp at hv
    · rw [Finset.eq_empty_iff_forall_notMem]
      simp only [inducedForcedComponentTag?, hh, hv, ↓reduceIte, true_iff]
      intro axis
      cases axis
      · exact hh
      · exact hv

/-- Acyclic forced sets give every induced component at least one valid tag. -/
theorem inducedForcedComponentTag?_isSome_of_isAcyclic {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    (inducedForcedComponentTag? C).isSome := by
  rcases induced_forced_connectedComponent_straight hacyc C with h | h
  · have hh : .horizontal ∈ inducedForcedComponentValidAxes C :=
      (horizontal_mem_inducedForcedComponentValidAxes_iff C).2 h
    simp [inducedForcedComponentTag?, hh]
  · by_cases hh : .horizontal ∈ inducedForcedComponentValidAxes C
    · simp [inducedForcedComponentTag?, hh]
    · have hv : .vertical ∈ inducedForcedComponentValidAxes C :=
        (vertical_mem_inducedForcedComponentValidAxes_iff C).2 h
      simp [inducedForcedComponentTag?, hh, hv]

/-- Which geometric side of a crop a frame half-edge crosses. -/
inductive CropFrameSide
  | top
  | right
  | bottom
  | left
  deriving DecidableEq

instance : Fintype CropFrameSide where
  elems := {.top, .right, .bottom, .left}
  complete := by intro side; cases side <;> simp

/-- Ambient coordinate edges with exactly one endpoint in the crop. -/
noncomputable def cropFrameEdgeFinset {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) : Finset (GridEdge m n) := by
  classical
  let R := Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)
  exact Finset.univ.filter fun edge =>
    (edge.primalEndpoints.1 ∈ R ∧ edge.primalEndpoints.2 ∉ R) ∨
      (edge.primalEndpoints.1 ∉ R ∧ edge.primalEndpoints.2 ∈ R)

@[simp] theorem mem_cropFrameEdgeFinset_iff {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (edge : GridEdge m n) :
    edge ∈ cropFrameEdgeFinset rowOffset colOffset hrows hcols ↔
      (edge.primalEndpoints.1 ∈
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) ∧
        edge.primalEndpoints.2 ∉
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)) ∨
      (edge.primalEndpoints.1 ∉
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) ∧
        edge.primalEndpoints.2 ∈
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)) := by
  classical
  simp [cropFrameEdgeFinset]

/-- A physical ambient grid edge leaving an offset crop.  The crop boundary
position is retained in addition to the ambient edge and its two endpoints. -/
structure CropFrameHalfEdge (p q m n rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (hp : 2 ≤ p) (hq : 2 ≤ q) where
  boundaryPosition : GridBoundaryPosition p q
  edge : GridEdge m n
  outside : GridVertex m n
  outside_not_mem : outside ∉
    Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)
  endpoints : edge.primalEndpoints =
      (gridOffsetEmbedding rowOffset colOffset hrows hcols
        (gridBoundaryVertex hp hq boundaryPosition), outside) ∨
    edge.primalEndpoints =
      (outside, gridOffsetEmbedding rowOffset colOffset hrows hcols
        (gridBoundaryVertex hp hq boundaryPosition))

namespace CropFrameHalfEdge

variable {p q m n rowOffset colOffset : Nat}
  {hrows : rowOffset + p ≤ m} {hcols : colOffset + q ≤ n}
  {hp : 2 ≤ p} {hq : 2 ≤ q}

/-- The endpoint of a frame half-edge retained by the crop. -/
def inside (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    GridVertex m n :=
  gridOffsetEmbedding rowOffset colOffset hrows hcols
    (gridBoundaryVertex hp hq e.boundaryPosition)

@[simp] theorem inside_mem_range
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    e.inside ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) :=
  ⟨gridBoundaryVertex hp hq e.boundaryPosition, rfl⟩

theorem inside_ne_outside
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    e.inside ≠ e.outside := by
  intro h
  exact e.outside_not_mem (h ▸ e.inside_mem_range)

/-- The physical edge joins the recorded inside and outside endpoints. -/
theorem adjacent_inside_outside
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    (gridGraph m n).Adj e.inside e.outside := by
  have hedge : (gridGraph m n).Adj e.edge.primalEndpoints.1
      e.edge.primalEndpoints.2 := by
    cases e.edge with
    | horizontal edge => exact horizontalPrimalEndpoints_adj edge
    | vertical edge => exact verticalPrimalEndpoints_adj edge
  rcases e.endpoints with h | h
  · simpa [inside, h] using hedge
  · have h' : (gridGraph m n).Adj e.outside e.inside := by
      simpa [inside, h] using hedge
    exact h'.symm

/-- Exact classification of the coordinate endpoints of a frame edge. -/
theorem endpoints_iff
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    (e.edge.primalEndpoints.1 = e.inside ∧
        e.edge.primalEndpoints.2 = e.outside) ∨
      (e.edge.primalEndpoints.1 = e.outside ∧
        e.edge.primalEndpoints.2 = e.inside) := by
  rcases e.endpoints with h | h
  · exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact Or.inr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Exactly the inside coordinate endpoint belongs to the crop. -/
theorem endpoint_range_classification
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    (e.edge.primalEndpoints.1 ∈
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) ∧
        e.edge.primalEndpoints.2 ∉
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)) ∨
      (e.edge.primalEndpoints.1 ∉
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) ∧
        e.edge.primalEndpoints.2 ∈
          Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)) := by
  rcases e.endpoints_iff with h | h
  · left
    simpa [h.1, h.2] using And.intro e.inside_mem_range e.outside_not_mem
  · right
    simpa [h.1, h.2] using And.intro e.outside_not_mem e.inside_mem_range

@[simp] theorem edge_mem_cropFrameEdgeFinset
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    e.edge ∈ cropFrameEdgeFinset rowOffset colOffset hrows hcols :=
  (mem_cropFrameEdgeFinset_iff rowOffset colOffset hrows hcols e.edge).2
    e.endpoint_range_classification

/-- Coordinate-exact classification into the four sides of the crop. -/
theorem side_classification
    (e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :
    (e.outside.1.val + 1 = e.inside.1.val ∧
        (gridBoundaryVertex hp hq e.boundaryPosition).1.val = 0) ∨
      (e.inside.2.val + 1 = e.outside.2.val ∧
        (gridBoundaryVertex hp hq e.boundaryPosition).2.val + 1 = q) ∨
      (e.inside.1.val + 1 = e.outside.1.val ∧
        (gridBoundaryVertex hp hq e.boundaryPosition).1.val + 1 = p) ∨
      (e.outside.2.val + 1 = e.inside.2.val ∧
        (gridBoundaryVertex hp hq e.boundaryPosition).2.val = 0) := by
  have hadj := e.adjacent_inside_outside
  change adjacent m n e.inside e.outside at hadj
  have hout := (mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols
    e.outside).not.mp e.outside_not_mem
  have hinRow : e.inside.1.val = rowOffset +
      (gridBoundaryVertex hp hq e.boundaryPosition).1.val := rfl
  have hinCol : e.inside.2.val = colOffset +
      (gridBoundaryVertex hp hq e.boundaryPosition).2.val := rfl
  rcases hadj with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
  · right; left
    have hrowVal := congrArg Fin.val hrow
    constructor <;> omega
  · right; right; right
    have hrowVal := congrArg Fin.val hrow
    constructor <;> omega
  · right; right; left
    have hcolVal := congrArg Fin.val hcol
    constructor <;> omega
  · left
    have hcolVal := congrArg Fin.val hcol
    constructor <;> omega

end CropFrameHalfEdge

/-- A physical frame edge is exactly an ambient coordinate edge admitting a
half-edge package with its inside endpoint numbered on the crop boundary. -/
theorem mem_cropFrameEdgeFinset_iff_exists_halfEdge
    {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (edge : GridEdge m n) :
    edge ∈ cropFrameEdgeFinset rowOffset colOffset hrows hcols ↔
      ∃ e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq,
        e.edge = edge := by
  classical
  constructor
  · intro hedge
    rw [mem_cropFrameEdgeFinset_iff] at hedge
    have hadj : (gridGraph m n).Adj edge.primalEndpoints.1
        edge.primalEndpoints.2 := by
      cases edge with
      | horizontal e => exact horizontalPrimalEndpoints_adj e
      | vertical e => exact verticalPrimalEndpoints_adj e
    rcases hedge with h | h
    · obtain ⟨w, hw⟩ := h.1
      have hwBoundary : IsGridBoundary w := by
        have hadj' : adjacent m n
            (gridOffsetEmbedding rowOffset colOffset hrows hcols w)
            edge.primalEndpoints.2 := by
          simpa only [hw, gridGraph] using hadj
        have hout := (mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols
          edge.primalEndpoints.2).not.mp h.2
        rcases hadj' with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
        · right; right; right
          have hrowVal := congrArg Fin.val hrow
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · right; right; left
          have hrowVal := congrArg Fin.val hrow
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · right; left
          have hcolVal := congrArg Fin.val hcol
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · left
          have hcolVal := congrArg Fin.val hcol
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition hp hq w hwBoundary
      let e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq :=
        { boundaryPosition := i
          edge := edge
          outside := edge.primalEndpoints.2
          outside_not_mem := h.2
          endpoints := Or.inl (by
            apply Prod.ext
            · simpa [hi] using hw.symm
            · rfl) }
      exact ⟨e, rfl⟩
    · obtain ⟨w, hw⟩ := h.2
      have hwBoundary : IsGridBoundary w := by
        have hadj' : adjacent m n
            (gridOffsetEmbedding rowOffset colOffset hrows hcols w)
            edge.primalEndpoints.1 := by
          simpa only [hw, gridGraph] using hadj.symm
        have hout := (mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols
          edge.primalEndpoints.1).not.mp h.1
        rcases hadj' with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
        · right; right; right
          have hrowVal := congrArg Fin.val hrow
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · right; right; left
          have hrowVal := congrArg Fin.val hrow
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · right; left
          have hcolVal := congrArg Fin.val hcol
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
        · left
          have hcolVal := congrArg Fin.val hcol
          simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at *
          omega
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition hp hq w hwBoundary
      let e : CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq :=
        { boundaryPosition := i
          edge := edge
          outside := edge.primalEndpoints.1
          outside_not_mem := h.1
          endpoints := Or.inr (by
            apply Prod.ext
            · rfl
            · simpa [hi] using hw.symm) }
      exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.edge_mem_cropFrameEdgeFinset

/-- Frame half-edges for an `(n - 3) x (n - 3)` total-three square crop. -/
abbrev ThreeSideCropFrameHalfEdge (n top bottom left right : Nat) (hn : 5 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3) :=
  CropFrameHalfEdge (n - 3) (n - 3) n n top left
    (by omega) (by omega) (by omega) (by omega)

end GridGraphs
