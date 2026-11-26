import GridGraphs.ResidueTwoUpper.StencilCancellation
import GridGraphs.ResidueTwoUpper.StencilBudget
import GridGraphs.ResidueTwoUpper.StencilTail
import GridGraphs.Results.ExactSquareFormula

/-! Physical unrestricted upper for the period-three dual. Eight-view
charges are summed directly on physical sites and patch origins. The
three signed families cancel, so no row-feasibility premise is needed. -/
namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

theorem corner_price (i : Nat) :
    cornerPrices.getD i 0 = if i=0 then -3422251782 else 0 := by
  have one : cornerPrices=(∅ : Std.HashMap Nat Int).insert 0 (-3422251782) := by rfl
  by_cases h : i=0
  · subst i; native_decide
  · simp [one,Std.HashMap.getD_insert,h,Ne.symm h]

theorem corner_nonpos (n : Nat) (p : Pos) (o : Nat) : twoCornerAt n p o ≤ 0 := by
  have le (g : Nat) : 4*cornerPrices.getD (atPos n 6 (image n g p)) 0 ≤ 0 := by
    rw [corner_price]; split_ifs <;> decide
  unfold twoCornerAt
  split_ifs
  · simp only [show List.range 8=[0,1,2,3,4,5,6,7] by decide,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil]
    linarith only [le 0,le 1,le 2,le 3,le 4,le 5,le 6,le 7]
  · decide

theorem root_charge {n : Nat} (hn : 12≤n) :
    twoCornerAt n (0,0) 4 = 8*cornerPrices.getD 0 0 := by
  have lo : axis n 6 0=0 := by unfold axis; split_ifs <;> omega
  have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; split_ifs <;> omega
  simp [twoCornerAt,show List.range 8=[0,1,2,3,4,5,6,7] by decide,corner_price,
    ResidueZero.image,atPos,lo,hi]

theorem physical_budget {n : Nat} (hn : 12≤n) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (star : ∀ p f nb o, inside n p → f<2 → nb<16 → o<5 → starOK n p f nb o → 0≤twoOrbitStar n p f nb o)
    (patch : ∀ p m, inside (n-2:Nat) p → m<512 → maskOK m → 0≤twoOrbitPatch n p m) :
    scale*(F.card:Int) ≤ rhs n := by
  let root : GridVertex n n := (⟨0,by omega⟩,⟨0,by omega⟩)
  obtain ⟨P,sink,step,covers⟩ := parent_exists F root acy
  have marg := physical_marginals_zero (n:=n) (by omega) F P step covers
  have positiveS : 0 ≤ ∑ v : GridVertex n n, twoOrbitStar n (coord v) (decide (v∈F)).toNat
      (neighbours F (coord v)) (outDir v (P v)) := by
    apply sum_nonneg; intro v _
    exact star _ _ _ _ (coord_inside v) (by cases decide (v∈F) <;> decide)
      (code_lt _) (outDir_lt ..) (starOK_physical F acy v _ (fun h => step _ h.symm))
  have positiveP : 0 ≤ ∑ a : origins n, twoOrbitPatch n (coord a) (maskAt F a) := by
    apply sum_nonneg; intro a _
    exact patch _ _ (coord_inside a) (Fin.isLt _) (physical_mask_ok F acy ..)
  let c (v : GridVertex n n) := twoCornerAt n (coord v) (outDir v (P v))
  have cb : (∑ v, c v) ≤ 8*cornerPrices.getD 0 0 := by
    have split := sum_erase_add (s:=univ) (mem_univ root) (f:=c)
    have neg := sum_nonpos (s:=univ.erase root) (fun v _ => corner_nonpos n (coord v) (outDir v (P v)))
    have rootVal : c root=8*cornerPrices.getD 0 0 := by
      unfold c; rw [sink]; simpa [root,coord,outDir] using root_charge (n:=n) hn
    change (∑ v ∈ univ.erase root, c v) ≤ 0 at neg
    linarith
  unfold twoMarginalSum at marg
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_mark,twoNormAt_sum] at marg
  change 0 ≤ ∑ a : origins n, twoOrbitPatch n (coord a) (physicalMask F a.1 a.2 _ _) at positiveP
  change (∑ v, twoCornerAt n (coord v) (outDir v (P v))) ≤ _ at cb
  unfold rhs
  linarith only [positiveS,positiveP,cb,marg]

theorem physical_upper_of_checks (star : twoStarCheck 20 && twoStarCheck 23)
    (patch : twoPatchCheck 20 && twoPatchCheck 23) (t : Nat) (F : Finset (GridVertex (20+3*t) (20+3*t)))
    (acy : (Bonds F).IsAcyclic) : 14*(F.card:Int) ≤ 2111+600*(t:Int)+42*(t:Int)^2 := by
  let n := 20+3*t
  have bound := physical_budget (n:=n) (by dsimp [n]; omega) F acy
    (fun _ _ _ _ hp hf hb ho h => star_nonneg_of_check star t hp hf hb ho h)
    (fun _ _ hp hm h => patch_nonneg_of_check patch t (by
      have ep : ((n-2:Nat):Int)=18+3*(t:Int) := by dsimp [n]; omega
      rwa [ep] at hp) hm h)
  have calcBudget := budget t
  change 14*rhs n=_ at calcBudget
  apply le_of_mul_le_mul_left (a:=scale) _ (by decide)
  linarith only [bound,calcBudget]

end GridGraphs.ResidueTwoUpper.Stencil
