import GridGraphs.Accounting.CarrierLayers.GapGlobalCapacity

/-!
# Excluding the zero induced/ambient slack profile

With `p=3` and `r=k+2`, the global capacity loss forbids shallow nonpure
carriers. Consequently different hole middles cannot reuse an inward carrier,
even inside one root-free gap. Empty blocks then force `c >= 2`.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Reusing an inward carrier at distinct open-side vertices makes the carrier
shallow. This holds on all four sides and does not require root separation. -/
theorem shared_inward_carrier_mem_nextRingCarriers {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (x y : GridVertex n n) (hx : OnOpenSide s x) (hy : OnOpenSide s y)
    (hne : x ≠ y) (w z : (↑F : Set (GridVertex n n)))
    (hwb : ¬ IsGridBoundary w.val) (hzb : ¬ IsGridBoundary z.val)
    (hxw : (gridGraph n n).Adj x w.val) (hyz : (gridGraph n n).Adj y z.val)
    (he : ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk z) :
    ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w ∈ nextRingCarriers F := by
  classical
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w
  have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hz : z ∈ C.supp := by
    dsimp [C]
    rw [he]
    simp [ConnectedComponent.mem_supp_iff]
  have hnonpure : C ∉ pureBoundaryCarriers F := fun h =>
    hwb ((mem_filter.mp h).2 w hw)
  change C ∈ nextRingCarriers F
  apply mem_filter.mpr
  refine ⟨mem_univ _, hnonpure, ?_⟩
  intro v hv
  by_cases hb : IsGridBoundary v.val
  · exact Or.inl hb
  right
  have hxy : x.1.val ≠ y.1.val ∨ x.2.val ≠ y.2.val := by
    by_contra h
    apply hne
    apply Prod.ext <;> apply Fin.ext <;> omega
  simp only [gridGraph, adjacent, Fin.ext_iff] at hxw hyz
  unfold OnOpenSide OnSide at hx hy
  unfold IsGridBoundary at hwb hzb hb
  unfold IsNextRing
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hw' := congrArg Fin.val (hr w hw)
    have hz' := congrArg Fin.val (hr z hz)
    have hv' := congrArg Fin.val (hr v hv)
    fin_cases s <;> norm_num at hx hy <;> omega
  · have hw' := congrArg Fin.val (hc w hw)
    have hz' := congrArg Fin.val (hc z hz)
    have hv' := congrArg Fin.val (hc v hv)
    fin_cases s <;> norm_num at hx hy <;> omega

/-- If there are no shallow nonpure carriers, arbitrary distinct hole middles
charge distinct carriers or isolates. No separation by preserved roots is needed. -/
theorem holes_charge_components_of_no_shallow_carriers {n : Nat} (hn : 5 ≤ n)
    (F S : Finset (GridVertex n n)) (hF : F.Nonempty)
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hgeom : ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph n n).Adj v z → IsGridBoundary z → z ∉ F) :
    (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card + S.card + 1 ≤
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent := by
  classical
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let G := (gridGraph n n).induce (↑F : Set _)
  let I := S.filter (fun v => ∀ z, ¬ H.Adj v z)
  let J := S \ I
  have hI := isolated_holes_card_add_one_le_components F I hF
    (fun v hv => (hgeom v (mem_filter.mp hv).1).2.1)
    (fun _ hv => (mem_filter.mp hv).2)
  have hwitness (v : J) : ∃ w : (↑F : Set (GridVertex n n)),
      ¬ IsGridBoundary w.val ∧ (gridGraph n n).Adj v.val w.val := by
    have hvS := (mem_sdiff.mp v.property).1
    have hvI := (mem_sdiff.mp v.property).2
    have hn : ¬ ∀ z, ¬ H.Adj v.val z := fun h => hvI (mem_filter.mpr ⟨hvS, h⟩)
    push Not at hn
    obtain ⟨w, hw⟩ := hn
    have hwF : w ∈ F := hw.2.resolve_left (hgeom v.val hvS).2.1
    exact ⟨⟨w, hwF⟩, fun hb => (hgeom v.val hvS).2.2 w hw.1 hb hwF, hw.1⟩
  let w : J → (↑F : Set (GridVertex n n)) := fun v => (hwitness v).choose
  have hwb (v : J) : ¬ IsGridBoundary (w v).val := (hwitness v).choose_spec.1
  have hadj (v : J) : (gridGraph n n).Adj v.val (w v).val := (hwitness v).choose_spec.2
  let f : J → G.ConnectedComponent := fun v => G.connectedComponentMk (w v)
  have hinj : Function.Injective f := by
    intro x y he
    by_contra hne
    have hm := shared_inward_carrier_mem_nextRingCarriers hn F hacyc s x.val y.val
      (hgeom _ (mem_sdiff.mp x.property).1).1 (hgeom _ (mem_sdiff.mp y.property).1).1
      (fun h => hne (Subtype.ext h)) (w x) (w y) (hwb x) (hwb y) (hadj x) (hadj y) he
    simp only [card_eq_zero.mp hzero, Finset.notMem_empty] at hm
  let D := univ.image f
  have hDcard : D.card = J.card := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  have hD : Disjoint D (pureBoundaryCarriers F) := by
    apply Finset.disjoint_left.mpr
    intro C hC hp
    obtain ⟨v, _, rfl⟩ := mem_image.mp hC
    have hw : w v ∈ (f v).supp := by simp [f, ConnectedComponent.mem_supp_iff]
    exact hwb v ((mem_filter.mp hp).2 (w v) hw)
  have havoid : ∀ u : (↑F : Set (GridVertex n n)), OnOpenSide s u.val →
      G.connectedComponentMk u ∉ D := by
    intro u hu hm
    obtain ⟨v, _, he⟩ := mem_image.mp hm
    have hvS := (mem_sdiff.mp v.property).1
    exact inward_hole_carrier_avoids_roots F hacyc s v.val (hgeom _ hvS).1
      (hgeom _ hvS).2.1 (w v) (hwb v) (hadj v) u hu he.symm
  have hbound := missing_side_roots_add_pure_add_extras_le_components
    F hacyc s hmissing D hD havoid
  have hpart := card_sdiff_add_card_inter S I
  have hsub : I ⊆ S := filter_subset _ _
  rw [inter_eq_right.mpr hsub] at hpart
  change J.card + I.card = S.card at hpart
  rw [hDcard] at hbound
  omega

/-- Excludes the actual numerical one-excess case
`(p,r,c,b)=(3,k+2,1,2k+6)`: with minimal induced count, at least two
ambient components are required. No root saturation or separated-hole
certificate is assumed. -/
theorem one_excess_minimal_induced_two_le_ambient {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2) :
    2 ≤ Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent := by
  have hzero : (nextRingCarriers F).card = 0 := by
    have h := one_excess_shallow_carriers_le_induced_slack (a := 0) hk F hacyc hp hf
      (by simpa using hr)
    omega
  obtain ⟨s, hmissing⟩ := exists_side_without_pure_carrier (by omega) F hacyc (by omega)
  obtain ⟨S, hS, hgeom⟩ := empty_block_middle_set (by omega) F s
  have hcharge := holes_charge_components_of_no_shallow_carriers (by omega) F S
    (card_pos.mp (by omega)) hacyc hzero s hmissing hgeom
  rw [hp, hr] at hcharge
  omega

/-- A sharp bound on the minimal-induced, connected, three-pure-carrier
branch. The elementary perimeter/deep budget only gives `T+6` here; the new
exclusion obtains nonreuse from actual deep-capacity loss, not a certificate. -/
theorem card_le_target_of_three_pure_minimal_induced_connected {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra hf
  have h := one_excess_minimal_induced_two_le_ambient hk F hacyc hp (by omega) hr
  omega

end GridGraphs.CarrierLayers
