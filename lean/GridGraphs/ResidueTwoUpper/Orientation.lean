import GridGraphs.Results.ExactSquareFormula

/-! Orient the actual forced edges toward a specified corner. Take paths
in a spanning-tree extension, then discard arrows on non-forced edges. -/
namespace GridGraphs.ResidueTwoUpper
open SimpleGraph

structure RootArrows {V : Type*} (G : SimpleGraph V) (root : V) where
  parent : V → Option V
  legal : ∀ {x y}, parent x = some y → G.Adj x y
  edge : ∀ {x y}, G.Adj x y → (parent x = some y ↔ parent y ≠ some x)
  sink : parent root = none

noncomputable def RootArrows.ofExtension {V : Type*} {G T : SimpleGraph V}
    (le : G ≤ T) (tree : T.IsTree) (root : V) : RootArrows G root := by
  classical
  let p (x : V) : T.Walk root x := ((isTree_iff_existsUnique_path.mp tree).2 root x).exists.choose
  have path (x : V) : (p x).IsPath := ((isTree_iff_existsUnique_path.mp tree).2 root x).exists.choose_spec
  let toward (x y : V) := G.Adj x y ∧ y ∈ (p x).support
  have unique {x y z} (hy : toward x y) (hz : toward x z) : y=z :=
    (tree.isAcyclic.eq_penultimate_of_adj_end (path _) (le hy.1) hy.2).trans
      (tree.isAcyclic.eq_penultimate_of_adj_end (path _) (le hz.1) hz.2).symm
  let par (x : V) := if h : ∃ y, toward x y then some h.choose else none
  have iff_par (x y : V) : par x = some y ↔ toward x y := by
    unfold par; split
    next h =>
      constructor
      · intro e; rw [←Option.some.inj e]; exact h.choose_spec
      · intro hy; exact congrArg some (unique h.choose_spec hy)
    next h => simp_all
  refine ⟨par,fun e => ((iff_par _ _).mp e).1,?_,?_⟩
  · intro x y xy
    change par x = some y ↔ ¬ par y = some x
    rw [iff_par,iff_par]
    simp only [toward,xy,xy.symm,true_and]
    exact ⟨tree.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath (path x) (path y) (le xy),
      tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (path x) (path y) (le xy)⟩
  · have nil : p root = .nil := Subtype.mk.inj <|
      (tree.isAcyclic.subsingleton_path root root).elim ⟨_,path root⟩ ⟨_,Walk.IsPath.nil⟩
    have empty : ¬∃ y, toward root y := by
      rintro ⟨y,adj,mem⟩
      rw [nil] at mem
      have eq : y=root := by simpa using mem
      exact adj.ne eq.symm
    simp [par,empty]

noncomputable def forestArrows {n} (hn : 0<n) (F : Finset (GridVertex n n))
    (acy : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (root : GridVertex n n) : RootArrows (forcedEdgeGraph (gridGraph n n) (↑F : Set _)) root :=
  let ext := (gridGraph_connected hn hn).exists_isTree_le_of_le_of_isAcyclic
    (forcedEdgeGraph_le _ _) acy
  RootArrows.ofExtension ext.choose_spec.1 ext.choose_spec.2.2 root

end GridGraphs.ResidueTwoUpper
