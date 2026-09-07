import GridGraphs.Accounting.CarrierLayers.RadialOneExcess

/-!
# Root-separated inward witnesses

Witnesses in the same root-free gap may share a carrier. A preserved root
strictly between two holes prevents this reuse, by interval filling.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- An intervening preserved side vertex separates inward carriers. This does
not require root saturation, ambient connectivity, or even a missing side. -/
theorem inward_carriers_distinct_of_root_between {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (x y : GridVertex n n)
    (hx : OnOpenSide s x) (hy : OnOpenSide s y) (hxU : x ∉ F)
    (u w z : (↑F : Set (GridVertex n n))) (hu : OnOpenSide s u.val)
    (hxu : sidePosition s x < sidePosition s u.val)
    (huy : sidePosition s u.val < sidePosition s y)
    (hwb : ¬ IsGridBoundary w.val) (hzb : ¬ IsGridBoundary z.val)
    (hxw : (gridGraph n n).Adj x w.val) (hyz : (gridGraph n n).Adj y z.val) :
    ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w ≠
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk z := by
  intro he
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w
  have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hz : z ∈ C.supp := by
    change z ∈ (((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w).supp
    rw [he]
    simp [ConnectedComponent.mem_supp_iff]
  have havoid := inward_hole_carrier_avoids_roots F hacyc s x hx hxU w hwb hxw u hu
  have huC : u ∈ C.supp := by
    by_cases hs : s.val < 2
    · have hgeom : w.val.1 = z.val.1 ∧ w.val.2.val ≤ u.val.2.val ∧
          u.val.2.val ≤ z.val.2.val ∧
          (gridGraph n n).Adj (w.val.1, u.val.2) u.val := by
        simp only [gridGraph, adjacent, Fin.ext_iff] at hxw hyz ⊢
        unfold OnOpenSide OnSide at hx hy hu
        unfold IsGridBoundary at hwb hzb
        simp only [sidePosition, if_pos hs] at hxu huy
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        right
        refine ⟨trivial, ?_⟩
        omega
      obtain ⟨hvF, hvC⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
        hacyc C hw hz hgeom.1 u.val.2 hgeom.2.1 hgeom.2.2.1
      exact C.mem_supp_of_adj_mem_supp hvC hgeom.2.2.2
    · have hgeom : w.val.2 = z.val.2 ∧ w.val.1.val ≤ u.val.1.val ∧
          u.val.1.val ≤ z.val.1.val ∧
          (gridGraph n n).Adj (u.val.1, w.val.2) u.val := by
        simp only [gridGraph, adjacent, Fin.ext_iff] at hxw hyz ⊢
        unfold OnOpenSide OnSide at hx hy hu
        unfold IsGridBoundary at hwb hzb
        simp only [sidePosition, if_neg hs] at hxu huy
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        left
        refine ⟨trivial, ?_⟩
        omega
      obtain ⟨hvF, hvC⟩ := induced_forced_connectedComponent_vertical_interval_of_le
        hacyc C hw hz hgeom.1 u.val.1 hgeom.2.1 hgeom.2.2.1
      exact C.mem_supp_of_adj_mem_supp hvC hgeom.2.2.2
  exact havoid (by simpa only [ConnectedComponent.mem_supp_iff, C] using huC)

/-- Count a set of actual extra carriers, disjoint from pure carriers and
missing-side root carriers. The input is a finset of components, not witnesses. -/
theorem missing_side_roots_add_pure_add_extras_le_components {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (D : Finset ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hD : Disjoint D (pureBoundaryCarriers F))
    (havoid : ∀ u : (↑F : Set (GridVertex n n)), OnOpenSide s u.val →
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u ∉ D) :
    (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card + D.card ≤
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let A := F.filter (OnOpenSide s)
  let P := pureBoundaryCarriers F
  let B := univ \ (D ∪ P)
  let root : A → (↑F : Set (GridVertex n n)) := fun u =>
    ⟨u.val, (mem_filter.mp u.property).1⟩
  have hmem (u : A) : root u ∈ (G.connectedComponentMk (root u)).supp := by
    simp [ConnectedComponent.mem_supp_iff]
  have hnonpure (u : A) : G.connectedComponentMk (root u) ∉ P := fun h =>
    hmissing _ h _ (hmem u) (mem_filter.mp u.property).2
  let f : A → B := fun u => ⟨G.connectedComponentMk (root u), by
    simp only [B, mem_sdiff, mem_univ, mem_union, true_and, not_or]
    exact ⟨havoid (root u) (mem_filter.mp u.property).2, hnonpure u⟩⟩
  have hinj : Function.Injective f := by
    intro u v he
    have heq : G.connectedComponentMk (root u) = G.connectedComponentMk (root v) :=
      congrArg Subtype.val he
    let C := G.connectedComponentMk (root u)
    have hu : root u ∈ C.supp := hmem u
    have hv : root v ∈ C.supp := by
      change root v ∈ (G.connectedComponentMk (root u)).supp
      rw [heq]
      exact hmem v
    have hn : ¬ ∀ w ∈ C.supp, IsGridBoundary w.val := by
      simpa only [P, pureBoundaryCarriers, mem_filter, mem_univ, true_and] using hnonpure u
    push Not at hn
    obtain ⟨w, hw, hwb⟩ := hn
    have hus := (mem_filter.mp u.property).2
    have hvs := (mem_filter.mp v.property).2
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    all_goals
      rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
      · have hur := congrArg Fin.val (hr _ hu)
        have hvr := congrArg Fin.val (hr _ hv)
        have hwr := congrArg Fin.val (hr _ hw)
        dsimp [root] at hur hvr
        unfold OnOpenSide OnSide at hus hvs
        unfold IsGridBoundary at hwb
        omega
      · have huc := congrArg Fin.val (hc _ hu)
        have hvc := congrArg Fin.val (hc _ hv)
        have hwc := congrArg Fin.val (hc _ hw)
        dsimp [root] at huc hvc
        unfold OnOpenSide OnSide at hus hvs
        unfold IsGridBoundary at hwb
        omega
  have hle := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hle
  have hpart := card_sdiff_add_card_inter (univ : Finset G.ConnectedComponent) (D ∪ P)
  rw [univ_inter, card_union_of_disjoint hD, card_univ] at hpart
  change A.card + P.card + D.card ≤ Fintype.card G.ConnectedComponent
  change A.card ≤ B.card at hle
  change B.card + (D.card + P.card) = Fintype.card G.ConnectedComponent at hpart
  omega

/-- Root-separated hole middles charge either distinct ambient isolates or
distinct extra induced carriers. Thus `q+p+|S|+1 <= r+c`, even away from
saturation. Selecting at most one middle per root-free gap is essential. -/
theorem separated_holes_charge_components {n : Nat}
    (F S : Finset (GridVertex n n)) (hF : F.Nonempty)
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hgeom : ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph n n).Adj v z → IsGridBoundary z → z ∉ F)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ∃ u ∈ F, OnOpenSide s u ∧
        ((sidePosition s x < sidePosition s u ∧ sidePosition s u < sidePosition s y) ∨
         (sidePosition s y < sidePosition s u ∧ sidePosition s u < sidePosition s x))) :
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
    have hxy : x.val ≠ y.val := fun h => hne (Subtype.ext h)
    have hxS := (mem_sdiff.mp x.property).1
    have hyS := (mem_sdiff.mp y.property).1
    obtain ⟨u, huF, hus, horder⟩ := hsep x.val hxS y.val hyS hxy
    rcases horder with ho | ho
    · exact inward_carriers_distinct_of_root_between F hacyc s x.val y.val
        (hgeom _ hxS).1 (hgeom _ hyS).1 (hgeom _ hxS).2.1
        ⟨u, huF⟩ (w x) (w y) hus ho.1 ho.2 (hwb x) (hwb y) (hadj x) (hadj y) he
    · exact inward_carriers_distinct_of_root_between F hacyc s y.val x.val
        (hgeom _ hyS).1 (hgeom _ hxS).1 (hgeom _ hyS).2.1
        ⟨u, huF⟩ (w y) (w x) hus ho.1 ho.2 (hwb y) (hwb x) (hadj y) (hadj x) he.symm
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

/-- The new geometric charge consumes the combined induced/ambient slack.
For a one-excess profile, any root-separated middle set has size at most
`a+m+2-p+d`. There is no saturation hypothesis. -/
theorem one_excess_separated_holes_slack {k : Nat} (hk : 5 ≤ k)
    (F S : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hgeom : ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v z → IsGridBoundary z → z ∉ F)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ∃ u ∈ F, OnOpenSide s u ∧
        ((sidePosition s x < sidePosition s u ∧ sidePosition s u < sidePosition s y) ∨
         (sidePosition s y < sidePosition s u ∧ sidePosition s u < sidePosition s x))) :
    ∃ a d e m : Nat, a + d + e = 3 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 2 + a ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 + d ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 + e ∧
      (F.filter (OnOpenSide s)).card + m = k ∧ m ≤ e + 1 ∧
      (pureBoundaryCarriers F).card + S.card ≤ a + m + 2 + d ∧
      (pureBoundaryCarriers F).card + S.card ≤ 6 := by
  obtain ⟨a, d, e, m, hs, hr, hc, hb, hm, hme, _, _⟩ :=
    one_excess_missing_side_slack hk F hacyc hp hcard s hmissing
  have hcharge := separated_holes_charge_components F S (card_pos.mp (by omega))
    hacyc s hmissing hgeom hsep
  exact ⟨a, d, e, m, hs, hr, hc, hb, hm, hme, by omega, by omega⟩

/-- A geometric score bound for any missing side, independent of `p <= 3`.
The chosen holes must be root-separated, not merely distinct empty blocks. -/
theorem missing_side_separated_holes_score {k : Nat} (hk : 3 ≤ k)
    (F S : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (hF : F.Nonempty)
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hgeom : ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v z → IsGridBoundary z → z ∉ F)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ∃ u ∈ F, OnOpenSide s u ∧
        ((sidePosition s x < sidePosition s u ∧ sidePosition s u < sidePosition s y) ∨
         (sidePosition s y < sidePosition s u ∧ sidePosition s u < sidePosition s x))) :
    3 * F.card + (pureBoundaryCarriers F).card + S.card ≤ 9 * k ^ 2 + 21 * k + 9 := by
  have hcharge := separated_holes_charge_components F S hF hacyc s hmissing hgeom hsep
  have hboundary := missing_side_root_boundary_budget hk F hacyc s
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

/-- Seven combined pure-carrier / root-separated-hole charges exclude one
excess. This is a conditional sharp bound, not existence of those charges. -/
theorem missing_side_card_le_target_of_separated_holes {k : Nat} (hk : 5 ≤ k)
    (F S : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hgeom : ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v z → IsGridBoundary z → z ∉ F)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ∃ u ∈ F, OnOpenSide s u ∧
        ((sidePosition s x < sidePosition s u ∧ sidePosition s u < sidePosition s y) ∨
         (sidePosition s y < sidePosition s u ∧ sidePosition s u < sidePosition s x)))
    (hseven : 7 ≤ (pureBoundaryCarriers F).card + S.card) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hscore := missing_side_separated_holes_score (by omega) F S
    (card_pos.mp (by omega)) hacyc s hmissing hgeom hsep
  omega

end GridGraphs.CarrierLayers
