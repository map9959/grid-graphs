import GridGraphs.Accounting.BoundarySix.Connected.GapDeepCorners

/-! Three straight carriers dominating the middle nine-square cannot contain
a corner of that square. A line through coordinate 2 misses the diagonal
samples 4, 7, 10; a line through 10 misses 2, 5, 8. Each other line can
dominate at most one sample in the missed triple. -/
namespace GridGraphs.Thirteen
open Finset SimpleGraph CarrierLayers CarrierLayers.Annulus BoundarySix BoundarySix.Connected

private abbrev V := GridVertex 13 13
private abbrev Line := Bool × Fin 13
private def coord (l : Line) (v : V) := if l.1 then v.1 else v.2
private def near (l : Line) (v : V) : Prop :=
  (coord l v).val ≤ l.2.val + 1 ∧ l.2.val ≤ (coord l v).val + 1

private theorem line_check : ∀ a b c : Line,
    (∀ v : V, ¬Mem v → near a v ∨ near b v ∨ near c v) →
    ∀ z : V, IsDeepCorner z → coord a z ≠ a.2 ∧ coord b z ≠ b.2 ∧ coord c z ≠ c.2 := by
  intro a b c cover z hz
  have diag (t : Fin 13) (lo : 2 ≤ t.val) (hi : t.val ≤ 10) :
      (t.val ≤ a.2.val+1 ∧ a.2.val ≤ t.val+1) ∨
      (t.val ≤ b.2.val+1 ∧ b.2.val ≤ t.val+1) ∨
      (t.val ≤ c.2.val+1 ∧ c.2.val ≤ t.val+1) := by
    simpa [near,coord] using cover (t,t) (by unfold Mem; dsimp; omega)
  have edge (l : Line) : (coord l z).val = 2 ∨ (coord l z).val = 10 := by
    unfold IsDeepCorner at hz
    unfold coord
    split <;> omega
  have e₁ := edge a
  have e₂ := edge b
  have e₃ := edge c
  have h₂ := diag 2 (by decide) (by decide)
  have h₄ := diag 4 (by decide) (by decide)
  have h₅ := diag 5 (by decide) (by decide)
  have h₇ := diag 7 (by decide) (by decide)
  have h₈ := diag 8 (by decide) (by decide)
  have h₁₀ := diag 10 (by decide) (by decide)
  refine ⟨?_,?_,?_⟩ <;> intro he <;> have eqv := congrArg Fin.val he <;> omega

private theorem inward_check : ∀ u : V, Second u → ∃ v : V, IsNextRing v ∧
    ∀ w : V, adjacent 13 13 v w → w = u ∨ IsNextRing w ∨ IsDeepCorner w := by
  intro u hu
  let inward (x : Fin 13) : Fin 13 := if x = 0 then 1 else if x = 12 then 11 else x
  refine ⟨(inward u.1, inward u.2),?_,?_⟩
  · unfold Second at hu
    simp only [IsNextRing,inward,Fin.ext_iff]
    split_ifs <;> omega
  · intro w hw
    unfold Second at hu
    simp only [adjacent,inward,Fin.ext_iff] at hw
    simp only [IsNextRing,IsDeepCorner,Prod.ext_iff,Fin.ext_iff]
    split_ifs at hw <;> omega

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 3000

theorem three_axes_exclude_gap (F : Finset V)
    (acy : (forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).IsAcyclic)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).ConnectedComponent = 1)
    (emptyRing : F.filter IsNextRing = ∅)
    (hd : (deepCarriers F).card = 3)
    (u : V) (hu : Second u) (hole : u ∉ F) : False := by
  classical
  have noRing (w : V) (hw : w ∈ F) : ¬IsNextRing w := by
    intro he
    have := mem_filter.mpr ⟨hw,he⟩
    rw [emptyRing] at this
    exact notMem_empty _ this
  obtain ⟨v,vr,hv⟩ := inward_check u hu
  obtain ⟨z,hz,adj⟩ := preserved_neighbor_of_one_forced_component (by decide) F hc v
    (fun h => noRing v h vr)
  have zc : IsDeepCorner z := by
    rcases hv z adj with rfl|hr|h
    · exact (hole hz).elim
    · exact (noRing _ hz hr).elim
    · exact h
  have hline (C : deepCarriers F) : ∃ l : Line,
      ∀ w ∈ C.val.supp, coord l w.val = l.2 := by
    rcases induced_forced_connectedComponent_straight acy C.val with ⟨r,h⟩|⟨c,h⟩
    · exact ⟨(true,r),h⟩
    · exact ⟨(false,c),h⟩
  choose axis onAxis using hline
  let e := Fintype.equivFinOfCardEq (show Fintype.card (deepCarriers F) = 3 by simpa using hd)
  let L (i : Fin 3) := axis (e.symm i)
  have cover (w : V) (hw : w ∈ F) (deep : ¬Mem w) :
      ∃ i, coord (L i) w = (L i).2 := by
    let C := ((gridGraph 13 13).induce (↑F : Set _)).connectedComponentMk ⟨w,hw⟩
    have hs : (⟨w,hw⟩ : (↑F : Set V)) ∈ C.supp := rfl
    have hC := deepCarrier_of_mem_deepVertices (by decide : 5 ≤ 13) F C
      ((mem_deepVertices (by decide) F C w).mpr ⟨hw,hs,deep⟩)
    exact ⟨e ⟨C,hC⟩,by simpa [L] using onAxis ⟨C,hC⟩ ⟨w,hw⟩ hs⟩
  have reach (w : V) (deep : ¬Mem w) : ∃ i, near (L i) w := by
    by_cases hw : w ∈ F
    · obtain ⟨i,hi⟩ := cover w hw deep
      exact ⟨i,by simp [near,hi]⟩
    obtain ⟨t,ht,adj⟩ := preserved_neighbor_of_one_forced_component (by decide) F hc w hw
    change adjacent 13 13 w t at adj
    have tdeep : ¬Mem t := by
      have hr := noRing t ht
      unfold adjacent at adj
      unfold IsNextRing at hr
      unfold Mem at *
      rcases adj with ⟨h,h'⟩|⟨h,h'⟩ <;> simp only [Fin.ext_iff] at h <;> omega
    obtain ⟨i,hi⟩ := cover t ht tdeep
    refine ⟨i,?_⟩
    unfold near
    rw [← hi]
    unfold coord adjacent at *
    split <;> rcases adj with ⟨h,h'⟩|⟨h,h'⟩ <;> simp only [Fin.ext_iff] at h <;> omega
  have h := line_check (L 0) (L 1) (L 2) (by
    intro w hw
    obtain ⟨i,hi⟩ := reach w hw
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)) z zc
  obtain ⟨i,hi⟩ := cover z hz (by unfold Mem; unfold IsDeepCorner at zc; omega)
  fin_cases i
  · exact h.1 hi
  · exact h.2.1 hi
  · exact h.2.2 hi

end GridGraphs.Thirteen
