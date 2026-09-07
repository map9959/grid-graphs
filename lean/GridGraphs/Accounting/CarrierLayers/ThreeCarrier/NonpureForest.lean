import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoRectangle

/-! # Forest ledger on the union of actual nonpure components -/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Restricting to a union of whole components preserves exactly that
component family, including singleton components. -/
theorem component_union_forest_ledger {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (A : Finset G.ConnectedComponent) :
    let T := univ.filter (fun v => G.connectedComponentMk v ∈ A)
    (G.induce (↑T : Set V)).edgeFinset.card + A.card = T.card := by
  classical
  let T := univ.filter (fun v => G.connectedComponentMk v ∈ A)
  let H := G.induce (↑T : Set V)
  let f : H →g G := (Embedding.induce (↑T : Set V)).toHom
  have hmap (C : H.ConnectedComponent) : C.map f ∈ A := by
    refine C.ind ?_
    intro v
    exact (mem_filter.mp v.property).2
  let g : H.ConnectedComponent → A := fun C => ⟨C.map f, hmap C⟩
  have hinj : Function.Injective g := by
    intro C D
    refine C.ind ?_
    intro u
    refine D.ind ?_
    intro v he
    have he' : G.connectedComponentMk u.val = G.connectedComponentMk v.val := congrArg Subtype.val he
    obtain ⟨p⟩ := ConnectedComponent.exact he'
    have hsupport : ∀ w ∈ p.support, w ∈ (↑T : Set V) := by
      intro w hw
      have hcomp : G.connectedComponentMk u.val = G.connectedComponentMk w :=
        ConnectedComponent.sound (p.takeUntil w hw).reachable
      exact mem_filter.mpr ⟨mem_univ _, hcomp ▸ (mem_filter.mp u.property).2⟩
    exact ConnectedComponent.sound ⟨p.induce (↑T : Set V) hsupport⟩
  have hsurj : Function.Surjective g := by
    intro C
    obtain ⟨v, hv⟩ := C.val.nonempty_supp
    have he := (ConnectedComponent.mem_supp_iff _ _).mp hv
    have hvT : v ∈ T := mem_filter.mpr ⟨mem_univ _, he ▸ C.property⟩
    refine ⟨H.connectedComponentMk ⟨v, hvT⟩, ?_⟩
    exact Subtype.ext he
  have hcard : Fintype.card H.ConnectedComponent = A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)
  have hledger := (hG.induce (↑T : Set V)).card_edgeFinset_add_card_connectedComponent
  change H.edgeFinset.card + Fintype.card H.ConnectedComponent = Fintype.card T at hledger
  rw [hcard, Fintype.card_coe] at hledger
  exact hledger

/-- Actual preserved vertices in nonpure carriers, on the original induced
vertex type. No cropped or reassigned carrier labels are introduced. -/
noncomputable def nonpureVertices {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (↑F : Set (GridVertex n n)) :=
  univ.filter fun v => ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk v ∉
    pureBoundaryCarriers F

noncomputable def nonpureGraph {n : Nat} (F : Finset (GridVertex n n)) :
    SimpleGraph (↑(nonpureVertices F) : Set (↑F : Set (GridVertex n n))) :=
  ((gridGraph n n).induce (↑F : Set _)).induce (↑(nonpureVertices F) : Set _)

/-- The exact ledger after removing all pure components, with every nonpure
FF edge retained. -/
theorem nonpure_forest_ledger {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (pureBoundaryVertices F).card +
      (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card) + (nonpureGraph F).edgeFinset.card = F.card := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let A := (univ : Finset G.ConnectedComponent) \ pureBoundaryCarriers F
  have hledger := component_union_forest_ledger G
    (induce_finset_isAcyclic_of_forcedEdgeGraph_isAcyclic _ F hacyc) A
  have hT : univ.filter (fun v => G.connectedComponentMk v ∈ A) = nonpureVertices F := by
    ext v
    simp [A, nonpureVertices, G]
  dsimp only at hledger
  rw [hT] at hledger
  have hA : A.card = Fintype.card G.ConnectedComponent - (pureBoundaryCarriers F).card := by
    simp [A, card_sdiff_of_subset (subset_univ _)]
  rw [hA] at hledger
  have hP : univ.filter (fun v => G.connectedComponentMk v ∈ pureBoundaryCarriers F) =
      pureBoundaryVertices F := by
    ext v
    simp only [mem_filter, mem_univ, true_and, pureBoundaryVertices, mem_biUnion, Set.mem_toFinset]
    constructor
    · intro hv
      exact ⟨G.connectedComponentMk v, hv, (ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
    · rintro ⟨C, hC, hv⟩
      exact ((ConnectedComponent.mem_supp_iff _ _).mp hv).symm ▸ hC
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset (↑F : Set (GridVertex n n))))
    (p := fun v => G.connectedComponentMk v ∈ pureBoundaryCarriers F)
  have hFcard : Fintype.card (↑F : Set (GridVertex n n)) = F.card := by simp
  rw [hP, card_univ, hFcard] at hpart
  change (pureBoundaryVertices F).card + (nonpureVertices F).card = F.card at hpart
  have hledger' : (nonpureGraph F).edgeFinset.card +
      (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card) = (nonpureVertices F).card := by
    convert hledger using 2
    congr 1
    ext e
    simp only [mem_edgeFinset]
    rfl
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
