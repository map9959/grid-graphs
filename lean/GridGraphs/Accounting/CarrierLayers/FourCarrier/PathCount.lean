import GridGraphs.Accounting.CarrierLayers.RadialSideGeometry

/-! # Counting carriers along a path

First occurrences inject into the path start and predecessors that are holes.
The ambient graph may have additional edges and need not be a forest.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

/-- A family of actual induced components met by a simple vertex path has at
most one more member than the number of holes on that path. -/
theorem components_le_path_holes_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset V)
    (A : Finset (G.induce (↑F : Set V)).ConnectedComponent)
    {m : Nat} (e : Fin m → V) (hinj : Function.Injective e)
    (hadj : ∀ (i j : Fin m), i.val + 1 = j.val → G.Adj (e i) (e j))
    (hcover : ∀ C ∈ A, ∃ i, ∃ hi : e i ∈ F,
      (⟨e i, hi⟩ : (↑F : Set V)) ∈ C.supp) :
    A.card ≤ ((univ.image e) \ F).card + 1 := by
  classical
  let I (C : A) := univ.filter fun i : Fin m =>
    ∃ hi : e i ∈ F, (⟨e i, hi⟩ : (↑F : Set V)) ∈ C.val.supp
  have hI (C : A) : (I C).Nonempty := by
    obtain ⟨i, hi, hC⟩ := hcover C.val C.property
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi, hC⟩⟩
  let first (C : A) := (I C).min' (hI C)
  have hfirst (C : A) : ∃ hi : e (first C) ∈ F,
      (⟨e (first C), hi⟩ : (↑F : Set V)) ∈ C.val.supp :=
    (mem_filter.mp (min'_mem (I C) (hI C))).2
  have hfirstinj : Function.Injective first := by
    intro C D he
    obtain ⟨hc, hC⟩ := hfirst C
    obtain ⟨hd, hD⟩ := hfirst D
    have hD' : (⟨e (first C), hc⟩ : (↑F : Set V)) ∈ D.val.supp := by
      simpa only [he] using hD
    exact Subtype.ext (ConnectedComponent.eq_of_common_vertex hC hD')
  let holes := univ.filter fun i : Fin m => e i ∉ F
  let starts := insert 0 (holes.image fun i => i.val + 1)
  have hstart (C : A) : (first C).val ∈ starts := by
    by_cases hzero : (first C).val = 0
    · simp [starts, hzero]
    have hpos : 0 < (first C).val := by omega
    let j : Fin m := ⟨(first C).val - 1, by have := (first C).isLt; omega⟩
    have hj : e j ∉ F := by
      intro hjF
      obtain ⟨hi, hC⟩ := hfirst C
      have hedge : (G.induce (↑F : Set V)).Adj
          ⟨e (first C), hi⟩ ⟨e j, hjF⟩ :=
        (hadj j (first C) (by dsimp [j]; omega)).symm
      have hjI : j ∈ I C := mem_filter.mpr
        ⟨mem_univ _, hjF, C.val.mem_supp_of_adj_mem_supp hC hedge⟩
      have hle := min'_le (I C) j hjI
      change first C ≤ j at hle
      have : (first C).val ≤ j.val := hle
      dsimp [j] at this
      omega
    apply mem_insert_of_mem
    exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, by dsimp [j]; omega⟩
  have hcount : A.card ≤ starts.card := by
    let f : A → starts := fun C => ⟨(first C).val, hstart C⟩
    have hf : Function.Injective f := by
      intro C D he
      exact hfirstinj (Fin.ext (congrArg Subtype.val he))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hholes : holes.card = ((univ.image e) \ F).card := by
    have he : holes.image e = (univ.image e) \ F := by
      ext v
      simp only [holes, mem_image, mem_filter, mem_univ, true_and, mem_sdiff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, rfl⟩, hi⟩
      · rintro ⟨⟨i, rfl⟩, hi⟩
        exact ⟨i, hi, rfl⟩
    rw [← he, card_image_of_injective _ hinj]
  have hs : starts.card ≤ holes.card + 1 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1)
  omega

end GridGraphs.CarrierLayers.FourCarrier
