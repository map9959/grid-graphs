import GridGraphs.Accounting.BoundaryFive.Rootless.LongRodGeometry

/-! # Extracting interval inventories from actual induced components -/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

/-- Straightness and interval filling provide the complete physical rod of
every actual induced component. No rod list or size is assumed. -/
theorem exists_representing_rod {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (C : ((gridGraph m m).induce F).ConnectedComponent) :
    ∃ R : Rod m, R.Represents F C := by
  classical
  obtain ⟨dir, axis, haxis⟩ : ∃ dir : Bool, ∃ axis : Fin m,
      ∀ v ∈ C.supp, (if dir = true then v.1.1 else v.1.2) = axis := by
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · exact ⟨true, r, hr⟩
    · exact ⟨false, c, hc⟩
  let coord : F → Fin m := fun v => if dir = true then v.1.2 else v.1.1
  let S : Finset (Fin m) := C.supp.toFinset.image coord
  obtain ⟨w, hw⟩ := C.nonempty_supp
  have hS : S.Nonempty := ⟨coord w, mem_image.mpr ⟨w, Set.mem_toFinset.mpr hw, rfl⟩⟩
  let lo := S.min' hS
  let hi := S.max' hS
  obtain ⟨u, hu, hul⟩ := mem_image.mp (min'_mem S hS)
  obtain ⟨v, hv, hvh⟩ := mem_image.mp (max'_mem S hS)
  have huC : u ∈ C.supp := Set.mem_toFinset.mp hu
  have hvC : v ∈ C.supp := Set.mem_toFinset.mp hv
  have hord : lo ≤ hi := min'_le S hi (max'_mem S hS)
  let R : Rod m := ⟨dir, axis, lo, hi, hord⟩
  refine ⟨R, ?_, ?_⟩
  · intro j hj
    have hj' : lo.val ≤ j.val ∧ j.val ≤ hi.val := mem_Icc.mp hj
    by_cases hd : dir = true
    · have huaxis : u.1.1 = axis := by simpa [hd] using haxis u huC
      have hvaxis : v.1.1 = axis := by simpa [hd] using haxis v hvC
      have hul' : u.1.2 = lo := by simpa [coord, hd] using hul
      have hvh' : v.1.2 = hi := by simpa [coord, hd] using hvh
      have h := induced_forced_connectedComponent_horizontal_interval_of_le hacyc C huC hvC
        (huaxis.trans hvaxis.symm) j (by rw [hul']; exact hj'.1) (by rw [hvh']; exact hj'.2)
      simpa [R, Rod.vertex, hd, huaxis] using h
    · have huaxis : u.1.2 = axis := by simpa [hd] using haxis u huC
      have hvaxis : v.1.2 = axis := by simpa [hd] using haxis v hvC
      have hul' : u.1.1 = lo := by simpa [coord, hd] using hul
      have hvh' : v.1.1 = hi := by simpa [coord, hd] using hvh
      have h := induced_forced_connectedComponent_vertical_interval_of_le hacyc C huC hvC
        (huaxis.trans hvaxis.symm) j (by rw [hul']; exact hj'.1) (by rw [hvh']; exact hj'.2)
      simpa [R, Rod.vertex, hd, huaxis] using h
  · intro z hz
    have hzS : coord z ∈ S := mem_image.mpr ⟨z, Set.mem_toFinset.mpr hz, rfl⟩
    refine ⟨coord z, mem_Icc.mpr ⟨min'_le S _ hzS, le_max' S _ hzS⟩, ?_⟩
    have ha := haxis z hz
    by_cases hd : dir = true
    · simp only [hd, if_true] at ha
      simp [R, Rod.vertex, coord, hd, Prod.ext_iff, ha]
    · simp only [if_neg hd] at ha
      simp [R, Rod.vertex, coord, hd, Prod.ext_iff, ha]

/-- The rod inventory is the actual preserved mass, counted exactly once. -/
theorem representing_rods_mass {m : Nat} (F : Finset (GridVertex m m))
    (R : ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent → Rod m)
    (hR : ∀ C, (R C).Represents (↑F : Set _) C) :
    (∑ C, (R C).length) = F.card := by
  classical
  let G := (gridGraph m m).induce (↑F : Set _)
  have he (C : G.ConnectedComponent) : (R C).length = C.supp.toFinset.card := by
    simpa only [Set.ncard_eq_toFinset_card'] using (hR C).card.symm
  simp only [he]
  have hcover : (univ.biUnion fun C : G.ConnectedComponent => C.supp.toFinset) =
      (univ : Finset (↑F : Set (GridVertex m m))) := by
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  have hd : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).Pairwise
      (fun C D => Disjoint C.supp.toFinset D.supp.toFinset) := by
    intro C _ D _ hne
    simpa using pairwise_disjoint_supp_connectedComponent G hne
  rw [← card_biUnion hd, hcover]
  simp

/-- Actual rooted-forest endpoint exclusion from four physical corner
records. The only extra packet data are four DISTINCT induced components,
each of size at most m-3 and each meeting a corner-neighbor boundary vertex.
No interval representation, longness, axis restriction, contact bound,
parallel spacing, orientation count, or deficit certificate is assumed.

CornerRoots derives these four records from four covered U corners in every
orientation, and hence removes the packet premises. AmbientEndpoint supplies
the ambient c=2 peeling bridge separately. -/
theorem rooted_endpoint_false_of_corner_packet {k m : Nat}
    (hk : 7 ≤ k) (hm : m + 2 = 3 * k)
    (F : Finset (GridVertex m m))
    (hacyc : (forcedEdgeGraph (gridGraph m m) (↑F : Set _)).IsAcyclic)
    (hroot : UniqueBoundaryRoots (m := m) (↑F : Set _))
    (hq : Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent = k)
    (hf : 3 * F.card + k = m * m)
    (corners : Finset ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent)
    (hfour : corners.card = 4)
    (hshort : ∀ C ∈ corners, C.supp.ncard + 3 ≤ m)
    (hnear : ∀ C ∈ corners, ∃ v ∈ C.supp, BoundarySix.Near v.1) : False := by
  classical
  choose R hR using exists_representing_rod hacyc
  have hmass : 3 * (∑ C, (R C).length) + k = m * m := by
    rw [representing_rods_mass F R hR]
    exact hf
  have hcap (C) : (R C).length ≤ m - 1 := by
    rw [← (hR C).card]
    exact strict_carrier_cap (by omega) hacyc hroot C
  have hshort' (C) (hC : C ∈ corners) : (R C).length + 3 ≤ m := by
    rw [← (hR C).card]
    exact hshort C hC
  have hlong := four_short_force_long k m hk hm hq (fun C => (R C).length)
    hcap corners hfour hshort' hmass
  have haxis (C) : 1 ≤ (R C).axis.val ∧ (R C).axis.val + 1 < m :=
    (hR C).interior_axis hroot (by have := (hlong C).2; omega)
  apply long_rods_endpoint_false k m hk hm hq R hcap haxis
    (fun C D hne => (hR C).separated hacyc hne (hR D))
    (fun C D _ hdir hdist => (hR C).two_step hacyc (hR D) hdir hdist)
    corners hfour hshort' ?_ hmass
  intro C hC
  obtain ⟨v, hv, hn⟩ := hnear C hC
  obtain ⟨j, _, he⟩ := (hR C).cover v hv
  rw [← he] at hn
  have ha := haxis C
  by_cases hd : (R C).horizontal = true <;>
    simp [Rod.vertex, hd, BoundarySix.Near] at hn <;> omega

end GridGraphs.BoundaryFive.Rootless
