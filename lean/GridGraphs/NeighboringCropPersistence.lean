import GridGraphs.GridBoundaryNonalternation
import GridGraphs.GridCropComponents
import GridGraphs.FourCropSurgery

/-!
# Persistence between neighboring corner crops

Two corner crops use different local coordinates even on their common
rectangle.  `NeighboringCropOverlapVertex` records both local coordinates and
the proof that they denote one ambient vertex.  This retained equality is the
key datum: equality of ambient component ancestors alone is insufficient to
identify crop components, since an ambient connecting path may leave either
crop.  All component conclusions below therefore require a path in the common
overlap.

Physical frame edges already have ambient `GridEdge` labels.  A repair edge can
be compared in the same way after its local coordinate edge is identified with
its ambient coordinate edge.  `NeighboringCropPhysicalEdgeChannel` deliberately
stores that fixed ambient label, so projecting an overlap channel to either
crop cannot rename or duplicate the edge.
-/

namespace GridGraphs

open SimpleGraph

/-- A vertex in the common overlap of two corner crops, with coordinates in
both crops and an equality of their ambient physical locations. -/
structure NeighboringCropOverlapVertex (n : Nat) (first second : FourCropCorner)
    (hn : 3 ≤ n) where
  firstVertex : GridVertex (n - 3) (n - 3)
  secondVertex : GridVertex (n - 3) (n - 3)
  ambient_eq : fourCropEmbedding n first hn firstVertex =
    fourCropEmbedding n second hn secondVertex

/-- The common overlap embedded at its physical ambient location. -/
def neighboringCropOverlapEmbedding (n : Nat) (first second : FourCropCorner)
    (hn : 3 ≤ n) :
    NeighboringCropOverlapVertex n first second hn ↪ GridVertex n n where
  toFun v := fourCropEmbedding n first hn v.firstVertex
  inj' := by
    intro v w h
    have hfirst : v.firstVertex = w.firstVertex :=
      (fourCropEmbedding n first hn).injective h
    have hsecondAmbient :
        fourCropEmbedding n second hn v.secondVertex =
          fourCropEmbedding n second hn w.secondVertex := by
      rw [← v.ambient_eq, ← w.ambient_eq]
      exact congrArg (fun x => x) h
    have hsecond : v.secondVertex = w.secondVertex :=
      (fourCropEmbedding n second hn).injective hsecondAmbient
    cases v
    cases w
    simp only at hfirst hsecond
    subst hfirst
    subst hsecond
    rfl

@[simp] theorem neighboringCropOverlapEmbedding_apply
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (v : NeighboringCropOverlapVertex n first second hn) :
    neighboringCropOverlapEmbedding n first second hn v =
      fourCropEmbedding n first hn v.firstVertex := rfl

/-- The grid graph on the physical common overlap. -/
abbrev neighboringCropOverlapGraph (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n) :=
  (gridGraph n n).comap (neighboringCropOverlapEmbedding n first second hn)

/-- Forced vertices and edges whose entire witness is retained in both crops. -/
abbrev neighboringCropOverlapInducedForcedGraph (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) :=
  (neighboringCropOverlapGraph n first second hn).induce
    ((neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)

/-- The induced forced graph in one of the four corner crops. -/
abbrev cornerCropInducedForcedGraph (n : Nat) (corner : FourCropCorner)
    (hn : 3 ≤ n) (F : Set (GridVertex n n)) :=
  (gridGraph (n - 3) (n - 3)).induce
    ((fourCropEmbedding n corner hn) ⁻¹' F)

/-- Forget the second coordinate description of an overlap vertex. -/
def neighboringCropOverlapToFirstHom (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) :
    neighboringCropOverlapInducedForcedGraph n first second hn F →g
      cornerCropInducedForcedGraph n first hn F where
  toFun v := ⟨v.1.firstVertex, v.2⟩
  map_rel' := by
    intro v w hvw
    exact (threeSideCropEmbedding_adj_iff n first.top first.bottom first.left
      first.right hn first.top_add_bottom first.left_add_right
      v.1.firstVertex w.1.firstVertex).1 hvw

/-- Forget the first coordinate description of an overlap vertex. -/
def neighboringCropOverlapToSecondHom (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) :
    neighboringCropOverlapInducedForcedGraph n first second hn F →g
      cornerCropInducedForcedGraph n second hn F where
  toFun v := ⟨v.1.secondVertex, by
    change fourCropEmbedding n second hn v.1.secondVertex ∈ F
    rw [← v.1.ambient_eq]
    exact v.2⟩
  map_rel' := by
    intro v w hvw
    apply (threeSideCropEmbedding_adj_iff n second.top second.bottom second.left
      second.right hn second.top_add_bottom second.left_add_right
      v.1.secondVertex w.1.secondVertex).1
    change (gridGraph n n).Adj
      (fourCropEmbedding n second hn v.1.secondVertex)
      (fourCropEmbedding n second hn w.1.secondVertex)
    rw [← v.1.ambient_eq, ← w.1.ambient_eq]
    exact hvw

/-- Component map from the common overlap to the first crop. -/
def neighboringCropComponentToFirst (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (C : (neighboringCropOverlapInducedForcedGraph n first second hn F).ConnectedComponent) :
    (cornerCropInducedForcedGraph n first hn F).ConnectedComponent :=
  C.map (neighboringCropOverlapToFirstHom n first second hn F)

/-- Component map from the common overlap to the second crop. -/
def neighboringCropComponentToSecond (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (C : (neighboringCropOverlapInducedForcedGraph n first second hn F).ConnectedComponent) :
    (cornerCropInducedForcedGraph n second hn F).ConnectedComponent :=
  C.map (neighboringCropOverlapToSecondHom n first second hn F)

/-- Inclusion of one corner crop's induced forced graph into the ambient
induced forced graph. -/
def cornerCropInducedForcedToAmbientHom (n : Nat) (corner : FourCropCorner)
    (hn : 3 ≤ n) (F : Set (GridVertex n n)) :
    cornerCropInducedForcedGraph n corner hn F →g (gridGraph n n).induce F where
  toFun v := ⟨fourCropEmbedding n corner hn v.1, v.2⟩
  map_rel' := by
    intro v w hvw
    exact (threeSideCropEmbedding_adj_iff n corner.top corner.bottom corner.left
      corner.right hn corner.top_add_bottom corner.left_add_right v.1 w.1).2 hvw

/-- Ambient ancestor of a component of a corner crop. -/
def cornerCropConnectedComponentAncestor (n : Nat) (corner : FourCropCorner)
    (hn : 3 ≤ n) (F : Set (GridVertex n n))
    (C : (cornerCropInducedForcedGraph n corner hn F).ConnectedComponent) :
    ((gridGraph n n).induce F).ConnectedComponent :=
  C.map (cornerCropInducedForcedToAmbientHom n corner hn F)

@[simp] theorem cornerCropConnectedComponentAncestor_mk
    (n : Nat) (corner : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (v : (fourCropEmbedding n corner hn) ⁻¹' F) :
    cornerCropConnectedComponentAncestor n corner hn F
        ((cornerCropInducedForcedGraph n corner hn F).connectedComponentMk v) =
      ((gridGraph n n).induce F).connectedComponentMk
        ⟨fourCropEmbedding n corner hn v.1, v.2⟩ := rfl

/-- The two images of one overlap component have compatible ambient
ancestors.  Membership supplies a concrete overlap vertex; merely knowing two
ambient ancestors are equal would not recover such a witness. -/
theorem neighboringCrop_mappedComponent_ancestors_eq
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (C : (neighboringCropOverlapInducedForcedGraph n first second hn F).ConnectedComponent)
    (x : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)
    (hx : x ∈ C.supp) :
    cornerCropConnectedComponentAncestor n first hn F
        (neighboringCropComponentToFirst n first second hn F C) =
      cornerCropConnectedComponentAncestor n second hn F
        (neighboringCropComponentToSecond n first second hn F C) := by
  rw [ConnectedComponent.mem_supp_iff] at hx
  rw [← hx]
  apply congrArg ((gridGraph n n).induce F).connectedComponentMk
  apply Subtype.ext
  exact x.1.ambient_eq

/-- A connecting path retained in the common overlap gives equal component
labels in each crop.  The corresponding labels also have the same ambient
ancestor.  The reachability hypothesis is essential; ancestor equality by
itself does not provide a path that stays in either crop. -/
theorem neighboringCrop_connectivity_persists
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)
    (hxy : (neighboringCropOverlapInducedForcedGraph n first second hn F).Reachable x y) :
    let xf := neighboringCropOverlapToFirstHom n first second hn F x
    let yf := neighboringCropOverlapToFirstHom n first second hn F y
    let xs := neighboringCropOverlapToSecondHom n first second hn F x
    let ys := neighboringCropOverlapToSecondHom n first second hn F y
    (cornerCropInducedForcedGraph n first hn F).connectedComponentMk xf =
        (cornerCropInducedForcedGraph n first hn F).connectedComponentMk yf ∧
      (cornerCropInducedForcedGraph n second hn F).connectedComponentMk xs =
        (cornerCropInducedForcedGraph n second hn F).connectedComponentMk ys ∧
      cornerCropConnectedComponentAncestor n first hn F
          ((cornerCropInducedForcedGraph n first hn F).connectedComponentMk xf) =
        cornerCropConnectedComponentAncestor n second hn F
          ((cornerCropInducedForcedGraph n second hn F).connectedComponentMk xs) := by
  dsimp only
  constructor
  · exact ConnectedComponent.sound
      (hxy.map (neighboringCropOverlapToFirstHom n first second hn F))
  constructor
  · exact ConnectedComponent.sound
      (hxy.map (neighboringCropOverlapToSecondHom n first second hn F))
  · rw [cornerCropConnectedComponentAncestor_mk,
      cornerCropConnectedComponentAncestor_mk]
    apply congrArg ((gridGraph n n).induce F).connectedComponentMk
    apply Subtype.ext
    exact x.1.ambient_eq

/-! ## Fixed physical edge channels -/

/-- A fixed ambient frame or repair edge together with a path witnessing its
channel entirely inside the common overlap.  The endpoint equality also says
that the physical edge itself lies in the overlap. -/
structure NeighboringCropPhysicalEdgeChannel (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n) where
  physicalEdge : GridEdge n n
  source : NeighboringCropOverlapVertex n first second hn
  target : NeighboringCropOverlapVertex n first second hn
  endpoints_eq : physicalEdge.primalEndpoints =
    (neighboringCropOverlapEmbedding n first second hn source,
      neighboringCropOverlapEmbedding n first second hn target) ∨
    physicalEdge.primalEndpoints =
      (neighboringCropOverlapEmbedding n first second hn target,
        neighboringCropOverlapEmbedding n first second hn source)
  witness : (neighboringCropOverlapGraph n first second hn).Walk source target

/-- The view of a fixed physical channel in one crop.  Its edge label remains
ambient, while its witness uses that crop's local coordinates. -/
structure CornerCropPhysicalEdgeChannel (n : Nat) (corner : FourCropCorner)
    (hn : 3 ≤ n) where
  physicalEdge : GridEdge n n
  source : GridVertex (n - 3) (n - 3)
  target : GridVertex (n - 3) (n - 3)
  endpoints_eq : physicalEdge.primalEndpoints =
    (fourCropEmbedding n corner hn source,
      fourCropEmbedding n corner hn target) ∨
    physicalEdge.primalEndpoints =
      (fourCropEmbedding n corner hn target,
        fourCropEmbedding n corner hn source)
  witness : (gridGraph (n - 3) (n - 3)).Walk source target

/-- Project an overlap channel to the first crop without changing its physical
edge label. -/
def NeighboringCropPhysicalEdgeChannel.toFirst
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    (channel : NeighboringCropPhysicalEdgeChannel n first second hn) :
    CornerCropPhysicalEdgeChannel n first hn where
  physicalEdge := channel.physicalEdge
  source := channel.source.firstVertex
  target := channel.target.firstVertex
  endpoints_eq := channel.endpoints_eq
  witness := channel.witness.map
    { toFun := NeighboringCropOverlapVertex.firstVertex
      map_rel' := by
        intro v w hvw
        exact (threeSideCropEmbedding_adj_iff n first.top first.bottom first.left
          first.right hn first.top_add_bottom first.left_add_right
          v.firstVertex w.firstVertex).1 hvw }

/-- Project an overlap channel to the second crop without changing its physical
edge label. -/
def NeighboringCropPhysicalEdgeChannel.toSecond
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    (channel : NeighboringCropPhysicalEdgeChannel n first second hn) :
    CornerCropPhysicalEdgeChannel n second hn where
  physicalEdge := channel.physicalEdge
  source := channel.source.secondVertex
  target := channel.target.secondVertex
  endpoints_eq := by
    rcases channel.endpoints_eq with h | h
    · left
      rw [h]
      apply Prod.ext <;> simp only
      · exact channel.source.ambient_eq
      · exact channel.target.ambient_eq
    · right
      rw [h]
      apply Prod.ext <;> simp only
      · exact channel.target.ambient_eq
      · exact channel.source.ambient_eq
  witness := channel.witness.map
    { toFun := NeighboringCropOverlapVertex.secondVertex
      map_rel' := by
        intro v w hvw
        apply (threeSideCropEmbedding_adj_iff n second.top second.bottom second.left
          second.right hn second.top_add_bottom second.left_add_right
          v.secondVertex w.secondVertex).1
        change (gridGraph n n).Adj
          (fourCropEmbedding n second hn v.secondVertex)
          (fourCropEmbedding n second hn w.secondVertex)
        rw [← v.ambient_eq, ← w.ambient_eq]
        exact hvw }

/-- A frame/repair channel whose physical edge and witness lie in the overlap
has literally the same ambient edge identity in both crop views. -/
theorem neighboringCrop_physicalEdgeChannel_identity
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    (channel : NeighboringCropPhysicalEdgeChannel n first second hn) :
    channel.toFirst.physicalEdge = channel.physicalEdge ∧
      channel.toSecond.physicalEdge = channel.physicalEdge ∧
      channel.toFirst.physicalEdge = channel.toSecond.physicalEdge := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Connectivity reflection or a seam-component witness -/

/-- Two distinct corner crops are neighbors when they share their horizontal
or vertical anchoring.  Thus diagonally opposite crops are not neighbors. -/
def FourCropCorner.Neighboring (first second : FourCropCorner) : Prop :=
  first ≠ second ∧ (first.top = second.top ∨ first.left = second.left)

/-- A vertex of the first crop lies on its seam relative to the second crop
when its physical ambient vertex is not retained by the second crop.  For
distinct horizontally or vertically neighboring corner crops this is exactly
the three-wide frame strip belonging only to the first crop. -/
def neighboringCropFirstSeamSet (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) :
    Set ((fourCropEmbedding n first hn) ⁻¹' F) :=
  {v | fourCropEmbedding n first hn v.1 ∉
    Set.range (fourCropEmbedding n second hn)}

/-- Coordinate form of the seam geometry.  For horizontal neighbors the
exclusive strip is on the left or right; for vertical neighbors it is on the
top or bottom.  The bounds are stated using crop offsets so no case-specific
coordinate renaming is needed. -/
theorem neighboringCropFirstSeamSet_geometry
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) (hneighbor : first.Neighboring second)
    (v : (fourCropEmbedding n first hn) ⁻¹' F) :
    v ∈ neighboringCropFirstSeamSet n first second hn F ↔
      (first.top = second.top ∧
        ((first.left < second.left ∧
            (fourCropEmbedding n first hn v.1).2.val < second.left) ∨
          (second.left < first.left ∧
            second.left + (n - 3) ≤
              (fourCropEmbedding n first hn v.1).2.val))) ∨
      (first.left = second.left ∧
        ((first.top < second.top ∧
            (fourCropEmbedding n first hn v.1).1.val < second.top) ∨
          (second.top < first.top ∧
            second.top + (n - 3) ≤
              (fourCropEmbedding n first hn v.1).1.val))) := by
  rw [neighboringCropFirstSeamSet, Set.mem_setOf_eq]
  change fourCropEmbedding n first hn v.1 ∉
      Set.range (gridOffsetEmbedding second.top second.left
        (show second.top + (n - 3) ≤ n by
          cases second <;> simp [FourCropCorner.top] <;> omega)
        (show second.left + (n - 3) ≤ n by
          cases second <;> simp [FourCropCorner.left] <;> omega)) ↔ _
  rw [mem_range_gridOffsetEmbedding_iff second.top second.left
    (show second.top + (n - 3) ≤ n by
      cases second <;> simp [FourCropCorner.top] <;> omega)
    (show second.left + (n - 3) ≤ n by
      cases second <;> simp [FourCropCorner.left] <;> omega)]
  rcases hneighbor with ⟨hne, hsame⟩
  cases first <;> cases second <;>
    simp [FourCropCorner.top, FourCropCorner.left, fourCropEmbedding,
      threeSideCropEmbedding] at hne hsame ⊢ <;> omega

/-- The forced components in the part of the first crop outside the second
crop.  These component labels are the frame/seam resources available when a
connection cannot be reflected to the second crop. -/
abbrev neighboringCropFirstSeamGraph (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) :=
  (cornerCropInducedForcedGraph n first hn F).induce
    (neighboringCropFirstSeamSet n first second hn F)

/-- A failed reflection carries concrete, label-preserving evidence: the
unique first-crop forest path meets a vertex outside the second crop, and that
vertex determines one seam component.  `component_eq` prevents the resource
from being renamed, while `path_unique` makes the witness independent of a
choice of connecting path. -/
structure NeighboringCropSeamComponentWitness (n : Nat)
    (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F) where
  path : (cornerCropInducedForcedGraph n first hn F).Walk
    (neighboringCropOverlapToFirstHom n first second hn F x)
    (neighboringCropOverlapToFirstHom n first second hn F y)
  path_isPath : path.IsPath
  seamVertex : (fourCropEmbedding n first hn) ⁻¹' F
  seamVertex_mem : seamVertex ∈ path.support
  seamVertex_not_second : seamVertex ∈
    neighboringCropFirstSeamSet n first second hn F
  component : (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent
  component_eq : component =
    (neighboringCropFirstSeamGraph n first second hn F).connectedComponentMk
      ⟨seamVertex, seamVertex_not_second⟩
  path_unique : ∀ q : (cornerCropInducedForcedGraph n first hn F).Walk
      (neighboringCropOverlapToFirstHom n first second hn F x)
      (neighboringCropOverlapToFirstHom n first second hn F y),
    q.IsPath → q = path

/-- If every vertex of a first-crop path is physically retained by the second
crop, the path induces a connection in the second crop.  This is the converse
lifting fact missing from mere overlap-path preservation. -/
theorem neighboringCrop_path_reflects_of_support_in_second
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)
    (p : (cornerCropInducedForcedGraph n first hn F).Walk
      (neighboringCropOverlapToFirstHom n first second hn F x)
      (neighboringCropOverlapToFirstHom n first second hn F y))
    (hp : ∀ v ∈ p.support,
      fourCropEmbedding n first hn v.1 ∈
        Set.range (fourCropEmbedding n second hn)) :
    (cornerCropInducedForcedGraph n second hn F).Reachable
      (neighboringCropOverlapToSecondHom n first second hn F x)
      (neighboringCropOverlapToSecondHom n first second hn F y) := by
  classical
  let P : Set ((fourCropEmbedding n first hn) ⁻¹' F) :=
    {v | v ∈ p.support}
  let secondVertex (v : P) : GridVertex (n - 3) (n - 3) :=
    Classical.choose (hp v.1 v.2)
  have secondVertex_eq (v : P) :
      fourCropEmbedding n second hn (secondVertex v) =
        fourCropEmbedding n first hn v.1.1 :=
    Classical.choose_spec (hp v.1 v.2)
  let secondMap :
      (cornerCropInducedForcedGraph n first hn F).induce P →g
        cornerCropInducedForcedGraph n second hn F :=
    { toFun := fun v => ⟨secondVertex v, by
        change fourCropEmbedding n second hn (secondVertex v) ∈ F
        rw [secondVertex_eq]
        exact v.1.2⟩
      map_rel' := by
        intro v w hvw
        apply (threeSideCropEmbedding_adj_iff n second.top second.bottom
          second.left second.right hn second.top_add_bottom
          second.left_add_right (secondVertex v) (secondVertex w)).1
        change (gridGraph n n).Adj
          (fourCropEmbedding n second hn (secondVertex v))
          (fourCropEmbedding n second hn (secondVertex w))
        rw [secondVertex_eq, secondVertex_eq]
        exact (threeSideCropEmbedding_adj_iff n first.top first.bottom
          first.left first.right hn first.top_add_bottom
          first.left_add_right v.1.1 w.1.1).2 hvw }
  let xf := neighboringCropOverlapToFirstHom n first second hn F x
  let yf := neighboringCropOverlapToFirstHom n first second hn F y
  let xP : P := ⟨xf, p.start_mem_support⟩
  let yP : P := ⟨yf, p.end_mem_support⟩
  obtain ⟨q⟩ := p.connected_induce_support xP yP
  have hreach := (q.map secondMap).reachable
  have hx : secondMap xP =
      neighboringCropOverlapToSecondHom n first second hn F x := by
    apply Subtype.ext
    change secondVertex xP = x.1.secondVertex
    apply (fourCropEmbedding n second hn).injective
    rw [secondVertex_eq]
    exact x.1.ambient_eq
  have hy : secondMap yP =
      neighboringCropOverlapToSecondHom n first second hn F y := by
    apply Subtype.ext
    change secondVertex yP = y.1.secondVertex
    apply (fourCropEmbedding n second hn).injective
    rw [secondVertex_eq]
    exact y.1.ambient_eq
  simpa only [hx, hy] using hreach

/-- Unconditional connectivity reflection for neighboring crops.  In a
first-crop forest, a connection between overlap vertices either survives in
the second crop or its unique path exposes a concretely labelled component of
the first crop's non-overlap frame/seam.  This does not assert that witnesses
for different connections are distinct. -/
theorem neighboringCrop_connectivity_reflects_or_seamComponent
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)
    (hxy : (cornerCropInducedForcedGraph n first hn F).Reachable
      (neighboringCropOverlapToFirstHom n first second hn F x)
      (neighboringCropOverlapToFirstHom n first second hn F y)) :
    (cornerCropInducedForcedGraph n second hn F).Reachable
        (neighboringCropOverlapToSecondHom n first second hn F x)
        (neighboringCropOverlapToSecondHom n first second hn F y) ∨
      Nonempty (NeighboringCropSeamComponentWitness
        n first second hn F x y) := by
  classical
  obtain ⟨p, hpPath⟩ := hxy.exists_isPath
  by_cases hall : ∀ v ∈ p.support,
      fourCropEmbedding n first hn v.1 ∈
        Set.range (fourCropEmbedding n second hn)
  · exact Or.inl (neighboringCrop_path_reflects_of_support_in_second
      n first second hn F x y p hall)
  · push_neg at hall
    obtain ⟨v, hvp, hvout⟩ := hall
    right
    exact ⟨{
      path := p
      path_isPath := hpPath
      seamVertex := v
      seamVertex_mem := hvp
      seamVertex_not_second := hvout
      component :=
        (neighboringCropFirstSeamGraph n first second hn F).connectedComponentMk
          ⟨v, hvout⟩
      component_eq := rfl
      path_unique := by
        intro q hq
        exact congrArg Subtype.val
          (hforest.path_unique (⟨q, hq⟩ :
            (cornerCropInducedForcedGraph n first hn F).Path _ _)
            (⟨p, hpPath⟩ :
              (cornerCropInducedForcedGraph n first hn F).Path _ _)) }⟩

/-- Empty seam resources are exactly the additional condition under which a
first-crop connection reflects to the second crop. -/
theorem neighboringCrop_connectivity_reflects_of_no_seamWitness
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F)
    (hxy : (cornerCropInducedForcedGraph n first hn F).Reachable
      (neighboringCropOverlapToFirstHom n first second hn F x)
      (neighboringCropOverlapToFirstHom n first second hn F y))
    (hno : IsEmpty (NeighboringCropSeamComponentWitness
      n first second hn F x y)) :
    (cornerCropInducedForcedGraph n second hn F).Reachable
      (neighboringCropOverlapToSecondHom n first second hn F x)
      (neighboringCropOverlapToSecondHom n first second hn F y) := by
  rcases neighboringCrop_connectivity_reflects_or_seamComponent
    n first second hn F hforest x y hxy with h | h
  · exact h
  · obtain ⟨witness⟩ := h
    exact (hno.false witness).elim

end GridGraphs
