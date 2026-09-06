import GridGraphs.Core.Forced

/-!
# Contiguous grid crops

Bounded coordinate offsets embed a smaller grid as a contiguous rectangle in
a larger grid.  In particular, deleting a total of three rows and three
columns from the four sides realizes an `(n - 3) x (n - 3)` grid inside the
`n x n` grid.
-/

namespace GridGraphs

open SimpleGraph

/-- Embed a grid as the contiguous rectangle whose top-left coordinate is
`(rowOffset, colOffset)`. -/
def gridOffsetEmbedding {p q m n : Nat} (rowOffset colOffset : Nat)
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n) :
    GridVertex p q ↪ GridVertex m n where
  toFun v :=
    (⟨rowOffset + v.1.val, lt_of_lt_of_le (Nat.add_lt_add_left v.1.isLt rowOffset) hrows⟩,
      ⟨colOffset + v.2.val, lt_of_lt_of_le (Nat.add_lt_add_left v.2.isLt colOffset) hcols⟩)
  inj' := by
    intro v w h
    apply Prod.ext <;> apply Fin.ext
    · have := congrArg (fun x => x.1.val) h
      simp only at this
      omega
    · have := congrArg (fun x => x.2.val) h
      simp only at this
      omega

@[simp] theorem gridOffsetEmbedding_fst_val {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (v : GridVertex p q) :
    ((gridOffsetEmbedding rowOffset colOffset hrows hcols v).1).val =
      rowOffset + v.1.val := rfl

@[simp] theorem gridOffsetEmbedding_snd_val {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (v : GridVertex p q) :
    ((gridOffsetEmbedding rowOffset colOffset hrows hcols v).2).val =
      colOffset + v.2.val := rfl

/-- A bounded coordinate offset preserves and reflects grid adjacency. -/
theorem gridOffsetEmbedding_adj_iff {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (v w : GridVertex p q) :
    (gridGraph m n).Adj
        (gridOffsetEmbedding rowOffset colOffset hrows hcols v)
        (gridOffsetEmbedding rowOffset colOffset hrows hcols w) ↔
      (gridGraph p q).Adj v w := by
  have hfst :
      (gridOffsetEmbedding rowOffset colOffset hrows hcols v).1 =
          (gridOffsetEmbedding rowOffset colOffset hrows hcols w).1 ↔
        v.1 = w.1 := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [gridOffsetEmbedding_fst_val] at hv
      omega
    · intro h
      apply Fin.ext
      simp only [gridOffsetEmbedding_fst_val]
      exact congrArg (fun x : Fin p => rowOffset + x.val) h
  have hsnd :
      (gridOffsetEmbedding rowOffset colOffset hrows hcols v).2 =
          (gridOffsetEmbedding rowOffset colOffset hrows hcols w).2 ↔
        v.2 = w.2 := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [gridOffsetEmbedding_snd_val] at hv
      omega
    · intro h
      apply Fin.ext
      simp only [gridOffsetEmbedding_snd_val]
      exact congrArg (fun x : Fin q => colOffset + x.val) h
  change adjacent m n
      (gridOffsetEmbedding rowOffset colOffset hrows hcols v)
      (gridOffsetEmbedding rowOffset colOffset hrows hcols w) ↔
    adjacent p q v w
  unfold adjacent
  rw [hfst, hsnd]
  simp only [gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val]
  omega

/-- Pulling the large grid back along a bounded offset gives exactly the
smaller grid. -/
theorem gridGraph_comap_gridOffsetEmbedding {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) :
    (gridGraph m n).comap (gridOffsetEmbedding rowOffset colOffset hrows hcols) =
      gridGraph p q := by
  ext v w
  exact gridOffsetEmbedding_adj_iff rowOffset colOffset hrows hcols v w

/-- The contiguous crop left after deleting `top`/`bottom` rows and
`left`/`right` columns, with three deleted in each direction. -/
def threeSideCropEmbedding (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3) :
    GridVertex (n - 3) (n - 3) ↪ GridVertex n n :=
  gridOffsetEmbedding top left (by omega) (by omega)

/-- The total-three crop preserves and reflects adjacency. -/
theorem threeSideCropEmbedding_adj_iff (n top bottom left right : Nat)
    (hn : 3 ≤ n) (hrows : top + bottom = 3)
    (hcols : left + right = 3) (v w : GridVertex (n - 3) (n - 3)) :
    (gridGraph n n).Adj
        (threeSideCropEmbedding n top bottom left right hn hrows hcols v)
        (threeSideCropEmbedding n top bottom left right hn hrows hcols w) ↔
      (gridGraph (n - 3) (n - 3)).Adj v w := by
  apply gridOffsetEmbedding_adj_iff

/-- Restricting a forced-edge graph to a contiguous offset rectangle is the
forced-edge graph of the preimage of the forced vertices. -/
theorem forcedEdgeGraph_comap_gridOffsetEmbedding {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (F : Set (GridVertex m n)) :
    (forcedEdgeGraph (gridGraph m n) F).comap
        (gridOffsetEmbedding rowOffset colOffset hrows hcols) =
      forcedEdgeGraph (gridGraph p q)
        ((gridOffsetEmbedding rowOffset colOffset hrows hcols) ⁻¹' F) := by
  ext v w
  change
    ((gridGraph m n).Adj
        (gridOffsetEmbedding rowOffset colOffset hrows hcols v)
        (gridOffsetEmbedding rowOffset colOffset hrows hcols w) ∧
      (gridOffsetEmbedding rowOffset colOffset hrows hcols v ∈ F ∨
        gridOffsetEmbedding rowOffset colOffset hrows hcols w ∈ F)) ↔ _
  rw [gridOffsetEmbedding_adj_iff]
  rfl

/-- Forced-edge acyclicity descends to every contiguous offset crop. -/
theorem forcedEdgeGraph_gridOffsetEmbedding_isAcyclic {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (F : Set (GridVertex m n))
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    (forcedEdgeGraph (gridGraph p q)
      ((gridOffsetEmbedding rowOffset colOffset hrows hcols) ⁻¹' F)).IsAcyclic := by
  rw [← forcedEdgeGraph_comap_gridOffsetEmbedding]
  exact hacyc.of_comap (gridOffsetEmbedding rowOffset colOffset hrows hcols)

/-- Every forced vertex surviving a nonempty contiguous crop can still be
realized as full-degree in a spanning tree of the crop. Thus restricting a
forced forest loses only deleted vertices, not feasibility of the retained
ones. -/
theorem exists_crop_tree_preserving_preimage {p q m n : Nat}
    (rowOffset colOffset : Nat) (hrows : rowOffset + p ≤ m)
    (hcols : colOffset + q ≤ n) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (F : Set (GridVertex m n))
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    ∃ T : SimpleGraph (GridVertex p q),
      T ≤ gridGraph p q ∧ T.IsTree ∧
        ∀ ⦃v : GridVertex p q⦄,
          gridOffsetEmbedding rowOffset colOffset hrows hcols v ∈ F →
            preservesIncidentEdges (gridGraph p q) T v := by
  apply exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic
    (gridGraph_connected hp hq)
  exact forcedEdgeGraph_gridOffsetEmbedding_isAcyclic
    rowOffset colOffset hrows hcols F hacyc

/-- Total-three crop specialization of forced-edge restriction. -/
theorem forcedEdgeGraph_comap_threeSideCropEmbedding
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n)) :
    (forcedEdgeGraph (gridGraph n n) F).comap
        (threeSideCropEmbedding n top bottom left right hn hrows hcols) =
      forcedEdgeGraph (gridGraph (n - 3) (n - 3))
        ((threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F) := by
  apply forcedEdgeGraph_comap_gridOffsetEmbedding

/-- Acyclicity of a forced-edge graph descends to an `(n - 3) x (n - 3)`
crop obtained by deleting three rows and columns in total from its sides. -/
theorem forcedEdgeGraph_threeSideCrop_isAcyclic
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) F).IsAcyclic) :
    (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
      ((threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F)).IsAcyclic := by
  rw [← forcedEdgeGraph_comap_threeSideCropEmbedding]
  exact hacyc.of_comap (threeSideCropEmbedding n top bottom left right hn hrows hcols)

/-- Total-three specialization: if the crop is nonempty, its retained forced
vertices are simultaneously realizable in a spanning tree of the
`(n - 3) x (n - 3)` crop. -/
theorem exists_threeSideCrop_tree_preserving_preimage
    (n top bottom left right : Nat) (hn : 4 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) F).IsAcyclic) :
    ∃ T : SimpleGraph (GridVertex (n - 3) (n - 3)),
      T ≤ gridGraph (n - 3) (n - 3) ∧ T.IsTree ∧
        ∀ ⦃v : GridVertex (n - 3) (n - 3)⦄,
          threeSideCropEmbedding n top bottom left right (by omega)
              hrows hcols v ∈ F →
            preservesIncidentEdges (gridGraph (n - 3) (n - 3)) T v := by
  apply exists_crop_tree_preserving_preimage top left
    (by omega) (by omega) (by omega) (by omega) F hacyc

end GridGraphs
