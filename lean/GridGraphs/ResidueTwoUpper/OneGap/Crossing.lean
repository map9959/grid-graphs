import GridGraphs.ResidueTwoUpper.OneGap.FanRay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil

private def transposeSet {n} (F : Finset (GridVertex n n)) := F.image Prod.swap
private def transposeMask (m : Fin 512) : Fin 512 := Fin.ofNat 512 (rotMask 7 m)
private theorem flipBit : ∀ m : Fin 512, ∀ q : Fin 9,
    bit (transposeMask m) q=bit m (3*(q.val%3)+q.val/3) := by native_decide
private theorem flipMask {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) :
    physicalMask (transposeSet F) c r hc hr = transposeMask (physicalMask F r c hr hc) := by
  have mark (p : Pos) : marked (transposeSet F) p=marked F p.swap := by
    apply Bool.eq_iff_iff.mpr
    simp only [marked,transposeSet,decide_eq_true_eq,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨v,hv,rfl⟩
    · rintro ⟨v,hv,e⟩
      refine ⟨v.swap,⟨v,hv,rfl⟩,?_⟩
      exact congrArg Prod.swap e
  have inj : ∀ a b : Fin 512, (∀ q : Fin 9, bit a q=bit b q) → a=b := by native_decide
  apply inj
  intro q
  let q' : Fin 9 := ⟨3*(q.val%3)+q.val/3,by have := q.isLt; omega⟩
  rw [flipBit]
  change bit _ q=bit _ q'
  rw [patch_bit,mark,patch_bit]
  congr 2 <;> ext <;> simp [offset,q'] <;> omega

private theorem transpose_ok : ∀ r c : Fin 3, ∀ m : Fin 512,
    stripeAllowed r c m → stripeAllowed c r (transposeMask m) := by native_decide

theorem east_step (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (r c : Nat)
    (hr : 6≤r ∧ r+9≤33+42*u) (hc : 6≤c ∧ c+11≤33+42*u)
    (phase : r%3=0 ∧ c%3=1)
    (clean : ∀ i : Fin 3, ∀ j : Fin 5,
      patchSlack F (⟨r+i,by have := i.isLt; omega⟩,⟨c+j,by have := j.isLt; omega⟩)=0)
    (seed : physicalMask F (r+1) c (by omega) (by omega)=73) :
    physicalMask F (r+1) (c+3) (by omega) (by omega)=73 := by
  have out := stripe_from_masks u (transposeSet F) c r hc hr ⟨phase.2,phase.1⟩ (by
    intro j i
    have hi := i.isLt; have hj := j.isLt
    let m := physicalMask F (r+i.val) (c+j.val) (by omega) (by omega)
    have z := clean i j
    change twoOrbitPatch ((35+42*u:Nat):Int) ((r+i.val:Nat),(c+j.val:Nat)) m=0 at z
    push_cast at z
    have b := bulk_stripe_allowed u (r+i) (c+j) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
      m (physical_mask_ok F acy ..) z
    have T := transpose_ok ⟨(r+i)%3,by omega⟩ ⟨(c+j)%3,by omega⟩ m
    rw [flipMask]
    simpa [stripeAllowed,m] using T (by simpa [stripeAllowed] using b))
    (by rw [flipMask,seed]; decide)
  rw [flipMask] at out
  have inv : ∀ m : Fin 512, transposeMask m=7 → m=73 := by native_decide
  exact inv _ out

/-- In a clean rectangle a north-row stripe (mask 7) cannot meet a
west-column stripe (mask 73) which travels along its output row. -/
theorem crossing_impossible (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (r c i j : Nat)
    (hr : 6≤r ∧ r+3*i+10≤33+42*u) (hc : 6≤c ∧ c+3*j+10≤33+42*u)
    (phase : r%3=1 ∧ c%3=1) (xi : 0 < i) (yj : 0 < j)
    (zs : ∀ a : origins (35+42*u),
      r≤a.1.val → a.1.val≤r+3*i+2 → c≤a.2.val → a.2.val≤c+3*j+2 → patchSlack F a=0)
    (v : physicalMask F r (c+3*j) (by omega) (by omega)=7)
    (h : physicalMask F (r+3*i) c (by omega) (by omega)=73) : False := by
  let x := c+3*j-1
  let y := r+3*i-1
  have xc : x+1=c+3*j := by dsimp [x]; omega
  have yr : y+1=r+3*i := by dsimp [y]; omega
  have V := stripe_ray u F acy r x i ⟨hr.1,by omega⟩ ⟨by omega,by omega⟩
    ⟨phase.1,by omega⟩ (fun s hs a b => by
      apply zs <;> dsimp <;> have := a.isLt <;> have := b.isLt <;> omega)
    (by simpa only [xc] using v)
  simp only [xc] at V
  have walk (t : Nat) (le : t≤j) : physicalMask F (y+1) (c+3*t) (by omega) (by omega)=73 := by
    induction t with
    | zero => simpa only [yr,Nat.mul_zero,Nat.add_zero] using h
    | succ t ih =>
      exact east_step u F acy y (c+3*t) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
        ⟨by omega,by omega⟩ (fun a b => by
          apply zs <;> dsimp <;> have := a.isLt <;> have := b.isLt <;> omega) (ih (by omega))
  have H := walk j le_rfl
  simp only [yr,V] at H
  exact (by decide : (7 : Fin 512) ≠ 73) H

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
