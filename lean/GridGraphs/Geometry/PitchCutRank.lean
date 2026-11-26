import GridGraphs.Accounting.ForestLedger
import GridGraphs.Core.Spanning

namespace GridGraphs.PitchCut
open SimpleGraph Finset
open scoped Sym2

/-- Only classes containing a terminal count towards the cap rank. -/
noncomputable def classes {V I : Type*} [Fintype I] (G : SimpleGraph V) (a : I → V) :
    Finset G.ConnectedComponent := by
  classical
  exact univ.image (fun i => G.connectedComponentMk (a i))

noncomputable def rank {V I : Type*} [Fintype I] (G : SimpleGraph V) (a : I → V) :=
  Fintype.card I - (classes G a).card

private theorem classes_le {V I : Type*} [Fintype I] {A B : SimpleGraph V}
    (sub : A ≤ B) (a : I → V) : (classes B a).card ≤ (classes A a).card := by
  classical
  let f := ConnectedComponent.map (Hom.ofLE sub)
  have eq : (classes A a).image f = classes B a := by
    unfold classes
    rw [image_image]; rfl
  rw [←eq]; exact card_image_le

/-- Delete real tooth spokes from one tree. The two cap partitions may
refine the remaining endpoint classes arbitrarily (e.g. omit unforced
tree edges). The cut graph need not consist of only two components. -/
theorem shared_rank {V I : Type*} [Fintype V] [Fintype I] [Nonempty I]
    (T A B : SimpleGraph V) (tree : T.IsTree) (a b : I → V)
    (inj : Function.Injective (fun i => s(a i,b i))) (spoke : ∀ i, T.Adj (a i) (b i))
    (ha : A ≤ T) (hb : B ≤ T)
    (av : ∀ i, ¬A.Adj (a i) (b i)) (bv : ∀ i, ¬B.Adj (a i) (b i)) :
    rank A a + rank B b ≤ Fintype.card I - 1 := by
  classical
  let D := univ.image (fun i => s(a i,b i))
  let H := T.deleteEdges (↑D : Set (Sym2 V))
  have avoids (G : SimpleGraph V) (sub : G ≤ T) (miss : ∀ i, ¬G.Adj (a i) (b i)) :
      G ≤ H := by
    intro x y h
    apply deleteEdges_adj.mpr
    refine ⟨sub h,?_⟩
    intro inD
    obtain ⟨i,_,eq⟩ := mem_image.mp (show s(x,y) ∈ D from inD)
    have hmem : s(x,y) ∈ G.edgeSet := h
    rw [←eq] at hmem
    exact miss i hmem
  let C := classes H a ∪ classes H b
  have touched (x : V) : H.connectedComponentMk x ∈ C := by
    let i₀ : I := Classical.arbitrary I
    have hit (f : I → V) (i : I) : H.connectedComponentMk (f i) ∈ classes H f :=
      mem_image_of_mem _ (mem_univ i)
    have init : H.connectedComponentMk (a i₀) ∈ C := mem_union_left _ (hit a i₀)
    obtain ⟨w⟩ := tree.connected.preconnected x (a i₀)
    suffices ∀ {u v}, T.Walk u v → H.connectedComponentMk v ∈ C →
        H.connectedComponentMk u ∈ C from this w init
    intro u v walk
    induction walk with
    | nil => exact id
    | @cons u y v e tail ih =>
      intro hv
      by_cases hd : s(u,y) ∈ D
      · obtain ⟨i,_,eq⟩ := mem_image.mp hd
        rcases Sym2.eq_iff.mp eq with ⟨h,_⟩|⟨_,h⟩ <;> rw [←h]
        · exact mem_union_left _ (hit a i)
        · exact mem_union_right _ (hit b i)
      · have he : H.Adj u y := deleteEdges_adj.mpr ⟨e,hd⟩
        rw [ConnectedComponent.sound he.reachable]; exact ih hv
  have un : C = univ := by
    apply eq_univ_of_forall
    intro c
    exact c.ind touched
  have cards := card_union_le (classes H a) (classes H b)
  change C.card ≤ _ at cards
  rw [un, card_univ] at cards
  have forest := tree.isAcyclic.anti (T.deleteEdges_le (↑D : Set (Sym2 V)))
  have edges := forest.card_edgeFinset_add_card_connectedComponent
  have subset : D ⊆ T.edgeFinset := by
    intro e he; obtain ⟨i,_,rfl⟩ := mem_image.mp he
    simpa using spoke i
  rw [edgeFinset_deleteEdges,card_sdiff_of_subset subset] at edges
  have dc : D.card = Fintype.card I := (card_image_of_injective _ inj).trans card_univ
  have bound := card_le_card subset
  have tc := tree.card_edgeFinset
  have ca := classes_le (avoids A ha av) a
  have cb := classes_le (avoids B hb bv) b
  have size (G : SimpleGraph V) (f : I → V) : (classes G f).card ≤ Fintype.card I :=
    card_image_le.trans_eq card_univ
  have := size A a
  have := size B b
  unfold rank
  change T.edgeFinset.card-D.card + Fintype.card H.ConnectedComponent = _ at edges
  omega

/-- Cut between two adjacent rows, with full-degree teeth on the lower
row. Each cap may use any subset of the physical tree on its side. -/
theorem grid_shared_rank {n k : Nat} {T A B : SimpleGraph (GridVertex n n)}
    (tree : IsSpanningSubtree (gridGraph n n) T) (u v : Fin n) (next : u.val+1=v.val)
    (col : Fin (k+1) ↪ Fin n)
    (full : ∀ i, preservesIncidentEdges (gridGraph n n) T (v,col i))
    (ha : A ≤ T) (hb : B ≤ T)
    (above : ∀ ⦃x y⦄, A.Adj x y → y.1.val ≤ u.val)
    (below : ∀ ⦃x y⦄, B.Adj x y → v.val ≤ x.1.val) :
    rank A (fun i => (u,col i)) + rank B (fun i => (v,col i)) ≤ k := by
  have sub := shared_rank T A B tree.2 (fun i => (u,col i)) (fun i => (v,col i))
  apply (show Fintype.card (Fin (k+1))-1 = k by simp) ▸ sub
  · intro i j eq
    rcases Sym2.eq_iff.mp eq with h|h <;> exact col.injective (congrArg Prod.snd h.1)
  · intro i
    exact (full i (Or.inr ⟨rfl,Or.inr next⟩ : (gridGraph n n).Adj (v,col i) (u,col i))).symm
  · exact ha
  · exact hb
  · intro i e; have : v.val ≤ u.val := above e; omega
  · intro i e; have : v.val ≤ u.val := below e; omega

end GridGraphs.PitchCut
