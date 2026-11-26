import GridGraphs.ResidueTwoUpper.OneGap.Projection

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil Finset

def parityAt {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) :
    occurrence n → Int :=
  Sum.elim (fun v => Parity.starBill n (coord v) (decide (v∈F)).toNat
    (neighbours F (coord v)) (outDir v (P v))) (fun a => Parity.patchBill n (coord a) (maskAt F a))

/-- The parity row prices the *same* exceptional occurrence as the rational
ledger. All the remaining prices, individually, are even. -/
theorem odd_at_defect (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (sink : P (nw u)=nw u) (corner : ∀ v, isCorner v → P v=v → v=nw u)
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (arr : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v))
    (d : occurrence (35+42*u)) (zero : ∀ x, x≠d → weightAt F P x=0) :
    parityAt F P d % 2 = 1 := by
  classical
  let n := 35+42*u
  have e : (n:Int)=35+42*(u:Int) := by dsimp [n]
  have ep : ((n-2:Nat):Int)=33+42*(u:Int) := by dsimp [n]; omega
  have rt (v : GridVertex n n) : Parity.rootOK n (coord v) (outDir v (P v)) := by
    by_cases hv : v=nw u
    · subst v; rw [sink]; simp [nw,Parity.rootOK,coord,outDir]
    · have nz : coord v ≠ (0,0) := fun eq => hv (coord_injective (a₂:=nw u) eq)
      simp only [Parity.rootOK,if_neg nz]
      split_ifs with h
      · have c : isCorner v := by simp only [coord] at h; unfold isCorner; omega
        have ne : v≠P v := fun eq => hv (corner v c eq.symm)
        simp only [outDir,if_neg ne]; split_ifs <;> decide
      · rfl
  have even (x : occurrence n) (ne : x≠d) : 2 ∣ parityAt F P x := by
    apply Int.dvd_of_emod_eq_zero
    have w := zero x ne
    cases x with
    | inl v =>
      let f : Fin 2 := ⟨(decide (v∈F)).toNat,by cases decide (v∈F) <;> decide⟩
      let b : Fin 16 := ⟨_,code_lt (fun i => marked F (shift (coord v) i))⟩
      let o : Fin 5 := ⟨_,outDir_lt v (P v)⟩
      have ok := starOK_physical F acy v (P v) (fun h => step _ h.symm)
      exact Parity.star_even Parity.stars_checked u _ (e ▸ coord_inside v) f b o
        (e ▸ ok) (e ▸ rt v) (Or.inl (e ▸ w))
    | inr a =>
      exact Parity.patch_even Parity.patches_checked u _ (ep ▸ coord_inside a) (maskAt F a)
        (physical_mask_ok F acy ..) (Or.inl (e ▸ w))
  have s : ∑ x, parityAt F P x = 1 := (Fintype.sum_sum_type _).trans
    (Parity.physical_sum_one (n:=n) (by dsimp [n]; omega) F P step arr)
  have h := sum_erase_add (s:=univ) (mem_univ d) (f:=parityAt F P)
  have ev := Finset.dvd_sum (s:=univ.erase d) (fun x hx => even x (mem_erase.mp hx).1)
  omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
