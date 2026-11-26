import GridGraphs.ResidueTwoUpper.ExceptionalProfiles
import GridGraphs.ResidueTwoUpper.ExceptionalParitySum
import GridGraphs.ResidueTwoUpper.ExceptionalParityTransport

namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil Finset

theorem odd_budget (st : Parity.starCheck) (pt : Parity.patchCheck)
    (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    let n := 35+42*u
    let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
    ∃ P : GridVertex n n → GridVertex n n, P root=root ∧
      (∀ v, P v≠v → (Bonds F).Adj v (P v)) ∧
      (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) ∧
      (∀ v, isCorner v → P v=v → v=root) ∧
      ∃ defect : occurrence n, weightAt F P defect=full ∧ ∀ x, x≠defect → weightAt F P x=0 := by
  dsimp only
  let n := 35+42*u
  let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
  obtain ⟨P,sink,step,edges,corners,values,counts⟩ := surviving_profiles u F acy score
  refine ⟨P,sink,step,edges,corners,?_⟩
  rcases counts with ⟨noHalf,one⟩|⟨_,noFull⟩
  · obtain ⟨x,hx⟩ := card_eq_one.mp one
    have iff_full (y) : weightAt F P y=full ↔ y=x := by
      simpa using Finset.ext_iff.mp hx y
    refine ⟨x,(iff_full x).mpr rfl,?_⟩
    intro y ne
    rcases values y with e|e|e
    · exact e
    · exact False.elim ((card_ne_zero_of_mem (mem_filter.mpr ⟨mem_univ y,e⟩)) noHalf)
    · exact False.elim (ne ((iff_full y).mp e))
  · have small (x) : weightAt F P x=0 ∨ weightAt F P x=half := by
      rcases values x with e|e|e
      · exact Or.inl e
      · exact Or.inr e
      · exact False.elim ((card_ne_zero_of_mem (mem_filter.mpr ⟨mem_univ x,e⟩)) noFull)
    have e : (n:Int)=35+42*(u:Int) := by dsimp [n]
    have ep : ((n-2:Nat):Int)=33+42*(u:Int) := by dsimp [n]; omega
    have rt (v : GridVertex n n) : Parity.rootOK n (coord v) (outDir v (P v)) := by
      by_cases r : v=root
      · subst v
        change P root=root at sink
        rw [sink]; simp [Parity.rootOK,coord,root,outDir]
      · have nz : coord v≠(0,0) := by
          intro eq; apply r; apply coord_injective; exact eq
        simp only [Parity.rootOK,if_neg nz]; split_ifs with cor
        · have h : isCorner v := by
            simp only [coord] at cor
            unfold isCorner; omega
          have ne : v≠P v := fun h' => r (corners _ h h'.symm)
          simp only [outDir,if_neg ne]; split_ifs <;> decide
        · rfl
    let s (v : GridVertex n n) := Parity.starBill n (coord v) (decide (v∈F)).toNat
      (neighbours F (coord v)) (outDir v (P v))
    let p (a : origins n) := Parity.patchBill n (coord a) (maskAt F a)
    have evenS (v : GridVertex n n) : (2:Int) ∣ s v := by
      apply Int.dvd_of_emod_eq_zero; unfold s; rw [e]
      let f : Fin 2 := ⟨(decide (v∈F)).toNat,by cases decide (v∈F) <;> decide⟩
      let nb : Fin 16 := ⟨neighbours F (coord v),code_lt _⟩
      let o : Fin 5 := ⟨outDir v (P v),outDir_lt ..⟩
      have ok := starOK_physical F acy v (P v) (fun h => step _ h.symm)
      have w := small (Sum.inl v)
      change twoOrbitStar n (coord v) f nb o=0 ∨ twoOrbitStar n (coord v) f nb o=half at w
      exact Parity.star_even st u _ (e ▸ coord_inside v) f nb o (e ▸ ok) (e ▸ rt v) (e ▸ w)
    have evenP (a : origins n) : (2:Int) ∣ p a := by
      apply Int.dvd_of_emod_eq_zero; unfold p; rw [e]
      have w := small (Sum.inr a)
      change twoOrbitPatch n (coord a) (maskAt F a)=0 ∨ twoOrbitPatch n (coord a) (maskAt F a)=half at w
      exact Parity.patch_even pt u _ (ep ▸ coord_inside a) (maskAt F a) (physical_mask_ok F acy ..) (e ▸ w)
    have div := dvd_add (Finset.dvd_sum (s:=univ) (fun x _ => evenS x))
      (Finset.dvd_sum (s:=univ) (fun x _ => evenP x))
    have odd : (∑ x, s x)+(∑ a, p a)=1 := Parity.physical_sum_one (n:=n) (by dsimp [n]; omega) F P step edges
    rw [odd] at div
    exact False.elim ((by decide : ¬(2:Int) ∣ 1) div)

end GridGraphs.ResidueTwoUpper.Exceptional
