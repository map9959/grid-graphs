import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

open scoped Sym2

namespace SimpleGraph

variable {V : Type*} (H : SimpleGraph V)

private instance componentAdjDecidable [DecidableRel H.Adj]
    (c : H.ConnectedComponent) : DecidableRel c.toSimpleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (H.Adj u.1 v.1))

private noncomputable instance componentEdgeSetFintype [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] (c : H.ConnectedComponent) : Fintype c.toSimpleGraph.edgeSet :=
  by
    letI : Fintype (Sym2 c) := Fintype.ofFinite _
    exact SimpleGraph.fintypeEdgeSet c.toSimpleGraph

/-- The edges of a finite graph are the disjoint union of the edges in its connected components. -/
private lemma sum_component_edgeFinset_card [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] :
    ∑ c : H.ConnectedComponent, c.toSimpleGraph.edgeFinset.card = H.edgeFinset.card := by
  classical
  let includeEdges (c : H.ConnectedComponent) : Sym2 c ↪ Sym2 V :=
    (Function.Embedding.subtype c.supp).sym2Map
  let componentEdges (c : H.ConnectedComponent) : Finset (Sym2 V) :=
    c.toSimpleGraph.edgeFinset.map (includeEdges c)
  let edgesByComponent :=
    (Finset.univ : Finset H.ConnectedComponent).sigma
      componentEdges
  have hmem (e : (c : H.ConnectedComponent) × Sym2 V) (he : e ∈ edgesByComponent) :
      e.2 ∈ H.edgeFinset := by
    rcases e with ⟨c, e⟩
    simp only [edgesByComponent, Finset.mem_sigma, Finset.mem_univ, true_and,
      componentEdges, Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.inductionOn with
    | _ u v =>
      have hadj : c.toSimpleGraph.Adj u v := mem_edgeFinset.mp he'
      exact mem_edgeFinset.mpr hadj
  have vertices_mem_component (c : H.ConnectedComponent) (e : Sym2 V)
      (he : e ∈ componentEdges c) : ∀ v ∈ e, v ∈ c.supp := by
    simp only [componentEdges, Finset.mem_map] at he
    obtain ⟨e', _, rfl⟩ := he
    intro v hv
    change v ∈ Sym2.map Subtype.val e' at hv
    rw [Sym2.mem_map] at hv
    obtain ⟨v', _, rfl⟩ := hv
    exact v'.property
  have hinj (a₁ : (c : H.ConnectedComponent) × Sym2 V)
      (h₁ : a₁ ∈ edgesByComponent) (a₂ : (c : H.ConnectedComponent) × Sym2 V)
      (h₂ : a₂ ∈ edgesByComponent)
      (heq : a₁.2 = a₂.2) : a₁ = a₂ := by
    rcases a₁ with ⟨c₁, e⟩
    rcases a₂ with ⟨c₂, e'⟩
    simp only at heq
    subst e'
    have hc : c₁ = c₂ := by
      simp only [edgesByComponent, Finset.mem_sigma, Finset.mem_univ, true_and] at h₁ h₂
      induction e using Sym2.inductionOn with
      | _ u v =>
        exact ConnectedComponent.eq_of_common_vertex
          (vertices_mem_component c₁ s(u, v) h₁ u (Sym2.mem_iff.mpr (Or.inl rfl)))
          (vertices_mem_component c₂ s(u, v) h₂ u (Sym2.mem_iff.mpr (Or.inl rfl)))
    subst c₂
    rfl
  have hsurj (e : Sym2 V) (he : e ∈ H.edgeFinset) :
      ∃ a, ∃ _ha : a ∈ edgesByComponent, a.2 = e := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : H.Adj u v := by simpa using he
      let c := H.connectedComponentMk u
      have hu : u ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
      have hv : v ∈ c.supp := c.mem_supp_of_adj_mem_supp hu huv
      refine ⟨⟨c, s(u, v)⟩, ?_, rfl⟩
      simp only [edgesByComponent, Finset.mem_sigma, Finset.mem_univ, true_and,
        componentEdges, Finset.mem_map]
      refine ⟨s(⟨u, hu⟩, ⟨v, hv⟩), ?_, rfl⟩
      exact mem_edgeFinset.mpr huv
  calc
    ∑ c : H.ConnectedComponent, c.toSimpleGraph.edgeFinset.card =
        ∑ c : H.ConnectedComponent, (componentEdges c).card := by
      apply Finset.sum_congr rfl
      intro c _
      simp [componentEdges]
    _ = edgesByComponent.card := (Finset.card_sigma ..).symm
    _ = H.edgeFinset.card := Finset.card_bij (fun a _ => a.2) hmem hinj hsurj

/-- A finite forest has `|V| - |components|` edges, in addition form. -/
theorem IsAcyclic.card_edgeFinset_add_card_connectedComponent
    [Fintype V] [DecidableEq V] [DecidableRel H.Adj] (hH : H.IsAcyclic) :
    H.edgeFinset.card + Fintype.card H.ConnectedComponent = Fintype.card V := by
  classical
  have htrees (c : H.ConnectedComponent) :
      c.toSimpleGraph.edgeFinset.card + 1 = Fintype.card c :=
    (hH.isTree_connectedComponent c).card_edgeFinset
  have hvertices : ∑ c : H.ConnectedComponent, Fintype.card c = Fintype.card V := by
    calc
      ∑ c : H.ConnectedComponent, Fintype.card c =
          ∑ c : H.ConnectedComponent, c.supp.toFinset.card := by
        apply Finset.sum_congr rfl
        intro c _
        let e : c ≃ c.supp := {
          toFun v := ⟨v, v.property⟩
          invFun v := ⟨v, v.property⟩
          left_inv _ := rfl
          right_inv _ := rfl }
        exact (Fintype.card_congr e).trans (Set.toFinset_card c.supp).symm
      _ = ((Finset.univ : Finset H.ConnectedComponent).biUnion
          fun c => c.supp.toFinset).card := by
        rw [Finset.card_biUnion]
        intro c₁ _ c₂ _ hne
        simpa using pairwise_disjoint_supp_connectedComponent H hne
      _ = Fintype.card V := by
        congr 1
        ext v
        simp [ConnectedComponent.mem_supp_iff]
  have hcomponents : Fintype.card H.ConnectedComponent =
      ∑ _c : H.ConnectedComponent, 1 := by simp
  rw [← H.sum_component_edgeFinset_card, hcomponents, ← Finset.sum_add_distrib]
  calc
    ∑ c : H.ConnectedComponent, (c.toSimpleGraph.edgeFinset.card + 1) =
        ∑ c : H.ConnectedComponent, Fintype.card c := Finset.sum_congr rfl fun c _ => htrees c
    _ = Fintype.card V := hvertices

/-- Subtractive form of the finite forest edge count. -/
theorem IsAcyclic.card_edgeFinset_eq_card_sub_card_connectedComponent
    [Fintype V] [DecidableEq V] [DecidableRel H.Adj] (hH : H.IsAcyclic) :
    H.edgeFinset.card = Fintype.card V - Fintype.card H.ConnectedComponent := by
  exact Nat.eq_sub_of_add_eq hH.card_edgeFinset_add_card_connectedComponent

end SimpleGraph
