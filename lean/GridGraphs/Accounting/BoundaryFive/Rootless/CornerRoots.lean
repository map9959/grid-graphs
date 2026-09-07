import GridGraphs.Accounting.BoundaryFive.Rootless.RodInventory

/-! # The four actual short corner-root carriers, with all orientations free -/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph CarrierLayers.FourCarrier

private def cornerChart {m : Nat} (flip : Bool) (s : Fin 4) (v : GridVertex m m) :
    GridVertex m m := sideChart s (if flip then (v.1.rev, v.2) else v)

private theorem cornerChart_injective {m : Nat} (flip : Bool) (s : Fin 4) :
    Function.Injective (cornerChart (m := m) flip s) := by
  intro x y h
  have h' := sideChart_injective s h
  cases flip <;> simp [Prod.ext_iff, Fin.ext_iff] at h' ⊢ <;> omega

private noncomputable def cornerChartIso {m : Nat} (flip : Bool) (s : Fin 4) :
    gridGraph m m ≃g gridGraph m m :=
  { Equiv.ofBijective (cornerChart flip s)
      ⟨cornerChart_injective flip s, Finite.surjective_of_injective (cornerChart_injective flip s)⟩ with
    map_rel_iff' := by
      intro x y
      change (gridGraph m m).Adj (cornerChart flip s x) (cornerChart flip s y) ↔ _
      unfold cornerChart
      rw [sideChart_adj]
      cases flip <;> simp [gridGraph, adjacent, Fin.ext_iff]
      omega }

private theorem cornerChart_boundary {m : Nat} (flip : Bool) (s : Fin 4) (v : GridVertex m m) :
    IsGridBoundary (cornerChart flip s v) ↔ IsGridBoundary v := by
  unfold cornerChart
  rw [sideChart_boundary]
  cases flip <;> simp [IsGridBoundary]
  omega

private theorem cornerChart_corner {m : Nat} (flip : Bool) (s : Fin 4) (v : GridVertex m m) :
    BoundarySix.Corner (cornerChart flip s v) ↔ BoundarySix.Corner v := by
  unfold cornerChart
  rw [sideChart_corner]
  cases flip <;> simp [BoundarySix.Corner]
  omega

private theorem near_has_chart {m : Nat} (hm : 4 ≤ m) (v : GridVertex m m)
    (hv : BoundarySix.Near v) :
    ∃ flip s, cornerChart flip s (⟨1, by omega⟩, ⟨0, by omega⟩) = v := by
  rcases hv with ⟨hr | hr, hc | hc⟩ | ⟨hc | hc, hr | hr⟩
  · refine ⟨false, 0, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨true, 0, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨false, 1, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨true, 1, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨false, 2, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨true, 2, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨false, 3, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega
  · refine ⟨true, 3, ?_⟩
    simp [cornerChart, sideChart, Prod.ext_iff, Fin.ext_iff]; omega

/-- Every actual corner-neighbor root carrier is short, in all eight
orientations. The destination corner is covered by BoundaryRooted; its two
possible root choices are retained. No other corner choice is normalized. -/
theorem near_root_component_short {m : Nat} (hm : 4 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hex : BoundaryRooted F) (hroot : UniqueBoundaryRoots F)
    (hcorners : ∀ z, BoundarySix.Corner z → z ∉ F)
    (C : ((gridGraph m m).induce F).ConnectedComponent)
    (v : F) (hv : v ∈ C.supp) (hn : BoundarySix.Near v.1) :
    C.supp.ncard + 3 ≤ m := by
  classical
  obtain ⟨flip, s, hvchart⟩ := near_has_chart hm v.1 hn
  let e := cornerChartIso (m := m) flip s
  let P : Set (GridVertex m m) := {x | e x ∈ F}
  let ef : forcedEdgeGraph (gridGraph m m) P ≃g forcedEdgeGraph (gridGraph m m) F :=
    { e.toEquiv with
      map_rel_iff' := by
        intro x y
        change ((gridGraph m m).Adj (e x) (e y) ∧ (e x ∈ F ∨ e y ∈ F)) ↔ _
        rw [e.map_rel_iff]
        rfl }
  let ei : ((gridGraph m m).induce P) ≃g ((gridGraph m m).induce F) :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by change e (e.symm x.1) ∈ F; rw [e.apply_symm_apply]; exact x.2⟩
      left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x.1
      right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x.1
      map_rel_iff' := by intro x y; exact e.map_rel_iff }
  have hbound (x) : IsGridBoundary (e x) ↔ IsGridBoundary x := cornerChart_boundary flip s x
  have hcorner (x) : BoundarySix.Corner (e x) ↔ BoundarySix.Corner x := cornerChart_corner flip s x
  have hPacyc := hacyc.comap ef.toHom ef.injective
  have hPunique : UniqueBoundaryRoots P := by
    intro x hx y hy hxb hyb hreach
    apply e.injective
    exact hroot _ hx _ hy ((hbound x).mpr hxb) ((hbound y).mpr hyb) (hreach.map ef.toHom)
  have hProoted : BoundaryRooted P := by
    intro x
    obtain ⟨u, hu, hub, hreach⟩ := hex (e x)
    refine ⟨e.symm u, ?_, ?_, ?_⟩
    · change e (e.symm u) ∈ F
      simpa using hu
    · exact (hbound _).mp (by simpa using hub)
    · have h := hreach.map ef.symm.toHom
      change (forcedEdgeGraph (gridGraph m m) P).Reachable (e.symm (e x)) (e.symm u) at h
      simpa using h
  have hPcorner (z) (hz : BoundarySix.Corner z) : z ∉ P :=
    hcorners (e z) ((hcorner z).mpr hz)
  have huP : (⟨1, by omega⟩, ⟨0, by omega⟩) ∈ P := by
    change cornerChart flip s _ ∈ F
    rw [hvchart]
    exact v.2
  let u : P := ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), huP⟩
  let D := ((gridGraph m m).induce P).connectedComponentMk u
  have huD : u ∈ D.supp := rfl
  have hcover : (⟨0, by omega⟩, ⟨m - 2, by omega⟩) ∈ P ∨
      (⟨1, by omega⟩, ⟨m - 1, by omega⟩) ∈ P := by
    have hz : (⟨0, by omega⟩, ⟨m - 1, by omega⟩) ∉ P :=
      hPcorner _ (by simp [BoundarySix.Corner]; omega)
    obtain ⟨w, hw, hadj⟩ := boundary_rooted_dominated hProoted _ hz
    have he : w = (⟨0, by omega⟩, ⟨m - 2, by omega⟩) ∨
        w = (⟨1, by omega⟩, ⟨m - 1, by omega⟩) := by
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
      simp only [Prod.ext_iff, Fin.ext_iff]
      dsimp at hadj
      omega
    exact he.elim (fun he => Or.inl (he ▸ hw)) (fun he => Or.inr (he ▸ hw))
  have hcap := covered_destination_component_cap hm hPacyc hPunique D huP huD hcover
  have hei : ei u = v := Subtype.ext hvchart
  have heD : ei.connectedComponentEquiv D = C := by
    change ((gridGraph m m).induce F).connectedComponentMk (ei u) = C
    rw [hei]
    exact hv
  have hcard : D.supp.ncard = C.supp.ncard := by
    change Nat.card D.supp = Nat.card C.supp
    simpa only [heD] using Nat.card_congr (D.isoEquivSupp ei)
  rw [hcard] at hcap
  omega

private theorem corner_neighbor_near {m : Nat} (hm : 4 ≤ m)
    (z u : GridVertex m m) (hz : BoundarySix.Corner z) (ha : (gridGraph m m).Adj z u) :
    BoundarySix.Near u := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at ha
  simp only [BoundarySix.Corner] at hz
  simp only [BoundarySix.Near]
  omega

private theorem corners_eq_of_common_neighbor {m : Nat} (hm : 4 ≤ m)
    (z w u : GridVertex m m) (hz : BoundarySix.Corner z) (hw : BoundarySix.Corner w)
    (ha : (gridGraph m m).Adj z u) (hb : (gridGraph m m).Adj w u) : z = w := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at ha hb
  simp only [BoundarySix.Corner] at hz hw
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- Four covered U corners give four DISTINCT actual induced carriers, each
short and meeting a near-corner boundary root. Distinctness follows from
UniqueBoundaryRoots and the fact that a near vertex cannot cover two corners.
No cyclic/reciprocal split or prescribed choice of a corner's root is used. -/
theorem four_short_corner_carriers {m : Nat} (hm : 4 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hex : BoundaryRooted F) (hroot : UniqueBoundaryRoots F)
    (hcorners : ∀ z, BoundarySix.Corner z → z ∉ F) :
    ∃ P : Finset ((gridGraph m m).induce F).ConnectedComponent,
      P.card = 4 ∧ (∀ C ∈ P, C.supp.ncard + 3 ≤ m) ∧
        ∀ C ∈ P, ∃ v ∈ C.supp, BoundarySix.Near v.1 := by
  classical
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨m - 1, by omega⟩
  let L : Finset (Fin m) := {a, b}
  let Q : Finset (GridVertex m m) := L ×ˢ L
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]; omega
  have hQcard : Q.card = 4 := by simp [Q, L, card_pair hab]
  have hQcorner (z : GridVertex m m) (hz : z ∈ Q) : BoundarySix.Corner z := by
    simp only [Q, L, mem_product, mem_insert, mem_singleton, a, b, Fin.ext_iff] at hz
    simp only [BoundarySix.Corner]
    omega
  choose u huF hadj using fun z : Q => boundary_rooted_dominated hex z.1
    (hcorners z.1 (hQcorner z.1 z.2))
  let G := (gridGraph m m).induce F
  let C : Q → G.ConnectedComponent := fun z => G.connectedComponentMk ⟨u z, huF z⟩
  have huC (z : Q) : (⟨u z, huF z⟩ : F) ∈ (C z).supp := rfl
  have hnear (z : Q) : BoundarySix.Near (u z) :=
    corner_neighbor_near hm z.1 (u z) (hQcorner z.1 z.2) (hadj z)
  have hboundary (z : Q) : IsGridBoundary (u z) := by
    have h := hnear z
    simp only [BoundarySix.Near, IsGridBoundary] at *
    tauto
  have hinj : Function.Injective C := by
    intro z w he
    have hwC : (⟨u w, huF w⟩ : F) ∈ (C z).supp := by rw [he]; exact huC w
    have hueq := hroot _ (huF z) _ (huF w) (hboundary z) (hboundary w)
      (induced_reachable_forced ((C z).reachable_of_mem_supp (huC z) hwC))
    apply Subtype.ext
    exact corners_eq_of_common_neighbor hm z.1 w.1 (u z) (hQcorner z.1 z.2)
      (hQcorner w.1 w.2) (hadj z) (by rw [hueq]; exact hadj w)
  let P : Finset G.ConnectedComponent := univ.image C
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]
    simpa using hQcard
  · intro D hD
    obtain ⟨z, _, rfl⟩ := mem_image.mp hD
    exact near_root_component_short hm hacyc hex hroot hcorners (C z) _ (huC z) (hnear z)
  · intro D hD
    obtain ⟨z, _, rfl⟩ := mem_image.mp hD
    exact ⟨⟨u z, huF z⟩, huC z, hnear z⟩

/-- Complete ACTUAL deep-rooted endpoint exclusion. The graph may have many
forced components, but every one has exactly one boundary F root. Four U
corners and the endpoint score suffice; there are no rod, orientation, packet,
spacing, or deficit hypotheses. AmbientEndpoint proves the ambient bridge
separately, using this theorem. -/
theorem rooted_deep_endpoint_false {k m : Nat} (hk : 7 ≤ k) (hm : m + 2 = 3 * k)
    (F : Finset (GridVertex m m))
    (hacyc : (forcedEdgeGraph (gridGraph m m) (↑F : Set _)).IsAcyclic)
    (hex : BoundaryRooted (m := m) (↑F : Set _))
    (hroot : UniqueBoundaryRoots (m := m) (↑F : Set _))
    (hcorners : ∀ z, BoundarySix.Corner z → z ∉ F)
    (hq : Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent = k)
    (hf : 3 * F.card + k = m * m) : False := by
  obtain ⟨P, hfour, hshort, hnear⟩ := four_short_corner_carriers (by omega) hacyc hex hroot hcorners
  exact rooted_endpoint_false_of_corner_packet hk hm F hacyc hroot hq hf P hfour hshort hnear

/-- The current k=1 mod 3 deep score is exactly the score excluded above. -/
theorem current_rooted_deep_endpoint_false {k : Nat} (hk : 7 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k - 2) (3 * k - 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k - 2) (3 * k - 2)) (↑F : Set _)).IsAcyclic)
    (hex : BoundaryRooted (m := 3 * k - 2) (↑F : Set _))
    (hroot : UniqueBoundaryRoots (m := 3 * k - 2) (↑F : Set _))
    (hcorners : ∀ z, BoundarySix.Corner z → z ∉ F)
    (hq : Fintype.card ((gridGraph (3 * k - 2) (3 * k - 2)).induce
      (↑F : Set _)).ConnectedComponent = k)
    (hf : F.card = 3 * k ^ 2 - 5 * k + 1 + (2 * k + 1) / 3) : False := by
  apply rooted_deep_endpoint_false hk (by omega) F hacyc hex hroot hcorners hq
  have he : 3 * ((2 * k + 1) / 3) = 2 * k + 1 := by omega
  have hsub : 3 * k ^ 2 - 5 * k + 5 * k = 3 * k ^ 2 := by
    apply Nat.sub_add_cancel
    nlinarith
  have hm : 3 * k - 2 + 2 = 3 * k := by omega
  nlinarith

end GridGraphs.BoundaryFive.Rootless
