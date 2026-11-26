import GridGraphs.ResidueZero.Stencil

namespace GridGraphs.ResidueZero

def representative (b j : Int) (p : Pos) : Pos := (rep b j p.1, rep b j p.2)

private theorem views {b j : Int} (p : Pos) (g : Nat) (δ t d : Int)
    (hδ : -2 ≤ δ ∧ δ ≤ 2) (ht : -2 ≤ t ∧ t ≤ 2)
    (hb : 19 ≤ b) (hj : 0 ≤ j) (fine : d=2 ∨ (δ=0 ∧ t=0 ∧ 0≤d ∧ d≤6))
    (coord : Bool) :
    let pick (x : Pos) := if coord then x.1 else x.2
    axis (b+3*j+δ) d (pick (image (b+3*j) g p)+t) =
    axis (b+δ) d (pick (image b g (representative b j p))+t) := by
  have h (i : Int) (f : Bool) :
      axis (b+3*j+δ) d (view f (b+3*j) i+t) =
      axis (b+δ) d (view f b (rep b j i)+t) := by
    rcases fine with rfl | ⟨rfl,rfl,hd⟩
    · exact transport_coarse hb hj hδ ht f
    · simpa using transport_fine (i:=i) hb hj hd f
  have a := h p.1 false
  have b' := h p.1 true
  have c := h p.2 false
  have e := h p.2 true
  simp only [view,Bool.false_eq_true,if_false,if_true] at *
  unfold image representative
  have hg : g%4=0 ∨ g%4=1 ∨ g%4=2 ∨ g%4=3 := by omega
  rcases hg with hg|hg|hg|hg <;> cases coord <;> by_cases hf : 4≤g <;>
    simp [hg,hf] <;> first | exact a | exact b' | exact c | exact e

private theorem query {b j : Int} (hb : 19 ≤ b) (hj : 0 ≤ j)
    (p : Pos) (g : Nat) (δ d : Int) (u : Pos)
    (hδ : -2 ≤ δ ∧ δ ≤ 2) (hu : -2 ≤ u.1 ∧ u.1 ≤ 2 ∧ -2 ≤ u.2 ∧ u.2 ≤ 2)
    (fine : d=2 ∨ (δ=0 ∧ u=(0,0) ∧ 0≤d ∧ d≤6)) :
    let a := image (b+3*j) g p+u
    let v := image b g (representative b j p)+u
    atPos (b+3*j+δ) d a = atPos (b+δ) d v ∧
    inside (b+3*j+δ) a = inside (b+δ) v := by
  have h₁ := views p g δ u.1 d hδ ⟨hu.1,hu.2.1⟩ hb hj (by rcases fine with h|⟨h,rfl,h'⟩ <;> tauto) true
  have h₂ := views p g δ u.2 d hδ hu.2.2 hb hj (by rcases fine with h|⟨h,rfl,h'⟩ <;> tauto) false
  simp only [if_true,Bool.false_eq_true,if_false] at h₁ h₂
  dsimp only
  constructor
  · simp [atPos,h₁,h₂]
  · have hd : 0 ≤ d := by rcases fine with rfl|⟨_,_,h,_⟩ <;> omega
    have ok {s i : Int} : (axis s d i ≠ -1) ↔ 0 ≤ i ∧ i<s := by
      unfold axis; split_ifs <;> omega
    apply Bool.eq_iff_iff.mpr
    simp only [inside,Bool.and_eq_true,decide_eq_true_eq,
      Prod.fst_add,Prod.snd_add]
    have hA := (ok (s:=b+3*j+δ) (i:=(image (b+3*j) g p).1+u.1)).symm
    have hB := (ok (s:=b+3*j+δ) (i:=(image (b+3*j) g p).2+u.2)).symm
    rw [h₁,ok] at hA
    rw [h₂,ok] at hB
    tauto

private def delta (d : Nat) : Pos := shift (0,0) d
private theorem shift_eq (p : Pos) (d : Nat) : shift p d = p+delta d := by
  unfold delta shift; split <;> ext <;> simp [sub_eq_add_neg]
private theorem delta_bound (d : Nat) :
    -2 ≤ (delta d).1 ∧ (delta d).1 ≤ 2 ∧ -2 ≤ (delta d).2 ∧ (delta d).2 ≤ 2 := by
  unfold delta shift; split <;> decide

private theorem common {b j : Int} (hb : 19 ≤ b) (hj : 0 ≤ j) (p : Pos) (g : Nat)
    (d : Int) (hd : 0 ≤ d ∧ d ≤ 6) :
    atPos (b+3*j) d (image (b+3*j) g p) = atPos b d (image b g (representative b j p)) := by
  simpa using (query hb hj p g 0 d 0 (by decide) (by decide) (.inr ⟨rfl,rfl,hd⟩)).1

private theorem neighbour {b j : Int} (hb : 19 ≤ b) (hj : 0 ≤ j) (p : Pos) (g d : Nat) :
    located (b+3*j) (shift (image (b+3*j) g p) d) =
    located b (shift (image b g (representative b j p)) d) := by
  have h := query hb hj p g 0 2 (delta d) (by decide) (delta_bound d) (.inl rfl)
  simp only [add_zero] at h
  simp [located,shift_eq,h.1,h.2]

theorem starLocation_transport {b j : Int} (hb : 19 ≤ b) (hj : 0 ≤ j) (p : Pos) (g : Nat) :
    starLocation (b+3*j) (image (b+3*j) g p) =
    starLocation b (image b g (representative b j p)) := by
  apply StarLocation.ext
  · exact common hb hj p g _ (by decide)
  · exact common hb hj p g _ (by decide)
  · funext d; exact neighbour hb hj p g d
  · funext q; dsimp [starLocation]; split
    · rename_i hq
      have h := query hb hj p g (-2) 2 (-offset q) (by decide)
        (by simp [offset]; omega) (.inl rfl)
      simpa [located,sub_eq_add_neg,h.1,h.2]
    · rfl

theorem patchLocation_transport {b j : Int} (hb : 19 ≤ b) (hj : 0 ≤ j) (p : Pos) (g : Nat) :
    patchLocation (b+3*j) (image (b+3*j) g p) =
    patchLocation b (image b g (representative b j p)) := by
  apply PatchLocation.ext
  · exact common hb hj p g _ (by decide)
  · exact common hb hj p g _ (by decide)
  · funext q; dsimp [patchLocation]; split
    · rename_i hq
      exact (query hb hj p g 2 2 (offset q) (by decide)
        (by simp [offset]; omega) (.inl rfl)).1
    · rfl
  · funext d; exact neighbour hb hj p g d

theorem orbitStar_transport (j : Nat) (p : Pos) (f nb o : Nat) :
    orbitStar (21+3*(j:Int)) p f nb o = orbitStar 21 (representative 21 j p) f nb o := by
  simp [orbitStar, starLocation_transport (b:=21) (by decide) (j:=(j:Int)) (by positivity)]

theorem orbitPatch_transport (j : Nat) (p : Pos) (m : Nat) :
    orbitPatch (21+3*(j:Int)) p m = orbitPatch 21 (representative 19 j p) m := by
  have h : 21+3*(j:Int)-2 = 19+3*j := by omega
  simp [orbitPatch,h,patchLocation_transport (b:=19) (by decide) (j:=(j:Int)) (by positivity)]

theorem starOK_transport (j : Nat) (p : Pos) (f nb o : Nat) :
    starOK (21+3*(j:Int)) p f nb o = starOK 21 (representative 21 j p) f nb o := by
  have h (d : Nat) := (query (b:=21) (by decide) (j:=(j:Int)) (by positivity)
    p 0 0 2 (delta d) (by decide) (delta_bound d) (.inl rfl)).2
  simp only [image,show ¬(0:Nat)≥4 by decide,if_false,Nat.zero_mod,add_zero,← shift_eq] at h
  simp [starOK,h]

end GridGraphs.ResidueZero
