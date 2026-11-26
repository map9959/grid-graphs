import GridGraphs.ResidueTwoUpper.ExceptionalSingle
import GridGraphs.ResidueTwoUpper.ExceptionalParityReplay
import GridGraphs.ResidueTwoUpper.ExceptionalCorners

/-! All physical consequences needed to enter the single-defect case.
The residual obligation is a structural exclusion of these marked and
oriented configurations; it contains no cardinality or maximum premise. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil

theorem single_defect (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    let n := 35+42*u
    let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
    ∃ P : GridVertex n n → GridVertex n n, P root=root ∧
      (∀ v, P v≠v → (Bonds F).Adj v (P v)) ∧
      (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) ∧
      (∀ v, isCorner v → P v=v → v=root) ∧
      ∃ d : occurrence n, weightAt F P d=full ∧ ∀ x, x≠d → weightAt F P x=0 :=
  odd_budget Parity.stars_checked Parity.patches_checked u F acy score

def SingleDefectExclusion (u : Nat) :=
  let n := 35+42*u
  let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
  ∀ (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n),
    (Bonds F).IsAcyclic → (∀ v, isCorner v → v∈F) →
    (∀ v w, (Bonds F).Adj v w → (Bonds F).Reachable root v) → P root=root →
    (∀ v, P v≠v → (Bonds F).Adj v (P v)) →
    (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) →
    (∀ v, isCorner v → P v=v → v=root) →
    ∀ d : occurrence n, weightAt F P d=full → (∀ x, x≠d → weightAt F P x=0) → False

theorem exceptional_input_of_single (u : Nat) (h : SingleDefectExclusion u) :
    ¬SquareMaskScore (35+42*u) (440+1020*u+588*u^2) := by
  rintro ⟨F,feas,score⟩
  have acy := mem_acyclicForcedSets.mp feas
  obtain ⟨P,root,step,edge,corners,d,w,others⟩ := single_defect u F acy score
  exact h F P acy (corners_marked u F acy score)
    (fun _ _ edge => (all_active_reachable u F acy score edge).1)
    root step edge corners d w others

private theorem noncorner_zero {n} (hn : 12≤n) (v : GridVertex n n) (hc : ¬isCorner v)
    (P : GridVertex n n → GridVertex n n) : cornerBill P v=0 := by
  have nu (i : Int) (hi : 0 ≤ i ∧ i<n) : (axis n 6 i).toNat=0 ↔ i=0 := by
    unfold axis; split_ifs <;> omega
  have van (g : Fin 8) : Stencil.cornerPrices.getD (atPos n 6 (image n g (coord v))) 0=0 := by
    have A := image_inside_iff n g (coord v)
    rw [coord_inside] at A
    simp only [inside,Bool.and_eq_true,decide_eq_true_eq] at A
    have r := nu _ ⟨A.1.1.1,A.1.1.2⟩; have c := nu _ ⟨A.1.2,A.2⟩
    rw [corner_price,if_neg]; intro e; unfold atPos at e
    have ex : (image n g (coord v)).1=0 ∧ (image n g (coord v)).2=0 := by omega
    apply hc; unfold isCorner
    have hv := v.1.isLt; have hw := v.2.isLt
    fin_cases g <;> norm_num [ResidueZero.image,coord] at ex <;> omega
  have all (g : Nat) (hg : g∈List.range 8) :
      4*Stencil.cornerPrices.getD (atPos n 6 (image n g (coord v))) 0=0 := by
    rw [van ⟨g,List.mem_range.mp hg⟩,mul_zero]
  simp [cornerBill,twoCornerAt,show List.range 8=[0,1,2,3,4,5,6,7] by decide,
    all 0 (by decide),all 1 (by decide),all 2 (by decide),all 3 (by decide),
    all 4 (by decide),all 5 (by decide),all 6 (by decide),all 7 (by decide)]

/-- Conversely, the structural configuration already has the forbidden
score: no extra mark count, or assumption of maximality, is necessary.
Thus the remaining geometric exclusion is equivalent to the desired
exceptional upper input. -/
theorem exceptional_input_iff_single (u : Nat) :
    (¬SquareMaskScore (35+42*u) (440+1020*u+588*u^2)) ↔ SingleDefectExclusion u := by
  refine ⟨?_,exceptional_input_of_single u⟩
  intro no F P acy _ _ sink step cov corners d wd zero
  let n := 35+42*u
  let root := nw u
  change P root=root at sink
  have charge : (∑ x, starSlack F P x)+(∑ x, patchSlack F x)=full := by
    have all : (∑ x, weightAt F P x)=weightAt F P d := Finset.sum_eq_single d
      (fun x _ ne => zero x ne) (by simp)
    exact (Fintype.sum_sum_type (Sum.elim (starSlack F P) (patchSlack F))).symm.trans (all.trans wd)
  have bills : (∑ x, cornerBill P x)=8*Stencil.cornerPrices.getD 0 0 := by
    rw [Finset.sum_eq_single root]
    · unfold cornerBill; rw [sink]; simpa [root,nw,coord,outDir] using
        root_charge (n:=n) (by dsimp [n]; omega)
    · intro v _ ne
      by_cases c : isCorner v
      · have fix : v≠P v := fun e => ne (corners v c e.symm)
        have nd : outDir v (P v)≠4 := by unfold outDir; rw [if_neg fix]; split_ifs <;> decide
        simp [cornerBill,twoCornerAt,nd]
      · exact noncorner_zero (n:=n) (by dsimp [n]; omega) v c P
    · simp
  have led := exact_ledger (n:=n) (by dsimp [n]; omega) F P step cov
  rw [charge,bills,sub_self,add_zero] at led
  have b := budget (5+14*u)
  rw [show 20+3*(5+14*u)=n by dsimp [n]; omega] at b
  refine no ⟨F,mem_acyclicForcedSets.mpr acy,?_⟩
  unfold full Stencil.scale at led; unfold Stencil.scale at b
  zify; push_cast at b ⊢; ring_nf at b ⊢
  omega

end GridGraphs.ResidueTwoUpper.Exceptional
