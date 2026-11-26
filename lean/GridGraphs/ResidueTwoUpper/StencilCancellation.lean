import GridGraphs.ResidueTwoUpper.StencilSums

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

def twoNormAt (tab : Std.HashMap Nat Int) (s d : Nat) (p : Pos) :=
  ((List.range 8).map fun g => tab.getD (atPos s d (image s g p)) 0).sum

def twoCornerAt (n : Nat) (p : Pos) (o : Nat) :=
  if o=4 then ((List.range 8).map fun g => 4*cornerPrices.getD (atPos n 6 (image n g p)) 0).sum
  else 0

theorem twoNormAt_sum (s d : Nat) (tab : Std.HashMap Nat Int) :
    (∑ v : GridVertex s s, twoNormAt tab s d (coord v)) = 8*plane s d (charge tab) := by
  simp [twoNormAt,show List.range 8=[0,1,2,3,4,5,6,7] by decide,sum_add_distrib,sum_norm_image]
  ring

def twoMarginalSum {n : Nat} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) :=
  (∑ v, (twoOrbitStar n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v)) -
    twoNormAt starNormPrices n 6 (coord v) - twoCornerAt n (coord v) (outDir v (P v)) +
    8*scale*((decide (v∈F)).toNat:Int))) +
  ∑ p : GridVertex (n-2) (n-2), (twoOrbitPatch n (coord p)
    (physicalMask F p.1 p.2 (by have := p.1.isLt; omega) (by have := p.2.isLt; omega)) -
    twoNormAt patchNormPrices (n-2) 5 (coord p))

private theorem turn_sum (g : Fin 8) (f : Nat → Int) :
    (∑ d ∈ range 4, f d) = ∑ d ∈ range 4, f (turn g d) := by
  fin_cases g <;> simp [sum_range_succ,turn] <;> ring

private theorem patchQ_sum (g : Fin 8) (f : Nat → Int) :
    (∑ q ∈ range 9, f q) = ∑ q : Fin 9, f (patchQ g q) := by
  have all : ∀ g : Fin 8, Function.Bijective (patchQ g) := by
    unfold Function.Bijective Function.Injective Function.Surjective
    native_decide
  rw [←Fin.sum_univ_eq_sum_range]
  exact (Equiv.ofBijective (patchQ g) (all g)).sum_comp (fun q => f q) |>.symm

private theorem views_sum (f : Nat → Int) :
    ((List.range 8).map f).sum = ∑ g : Fin 8, f g := by
  rw [Fin.sum_univ_eq_sum_range]
  simp [sum_range_succ,show List.range 8=[0,1,2,3,4,5,6,7] by decide]
  ring

private def starMarg {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (v : GridVertex n n) (g : Fin 8) :=
  (∑ d ∈ range 4, twoPortF F P g v d) + ∑ q : Fin 9, twoCoverF F g v q
private def patchMarg {n} (F : Finset (GridVertex n n)) (v : origins n) (g : Fin 8) :=
  (∑ d ∈ range 4, twoStripF F g v d) - ∑ q : Fin 9, twoSlotF F g v q

private theorem star_remove {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (v : GridVertex n n) :
    twoOrbitStar n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v)) -
    twoNormAt starNormPrices n 6 (coord v) - twoCornerAt n (coord v) (outDir v (P v)) +
    8*scale*((decide (v∈F)).toNat:Int) = ∑ g, starMarg F P v g := by
  let f := (decide (v∈F)).toNat
  let o := outDir v (P v)
  let p := coord v
  let nb := neighbours F p
  let c (g : Fin 8) := if o=4 then 4*cornerPrices.getD (atPos n 6 (image n g p)) 0 else 0
  have cor : twoCornerAt n p o = ∑ g, c g := by
    unfold twoCornerAt; by_cases h : o=4 <;> simp [h,c,views_sum]
  have h (g : Fin 8) :
      twoStarBill (starLocation n (image n g p)) f (rotBits g nb) (turnOut g o) =
        starNormPrices.getD (atPos n 6 (image n g p)) 0 - scale*(f:Int) +
          c g + starMarg F P v g := by
    have oo : turnOut g o=4 ↔ o=4 := by
      by_cases ho : o=4
      · simp [ho,turnOut]
      · have lt : turn g o < 4 := Nat.mod_lt _ (by decide)
        simp [turnOut,ho,show turn g o ≠ 4 by omega]
    unfold twoStarBill starMarg
    rw [turn_sum g (twoPort _ _ _ _),patchQ_sum g (twoCoverTerm _ _ _)]
    simp only [starLocation,oo,c,twoPortF,twoCoverF,nb,p,f,o,add_assoc]
  change twoOrbitStar n p f nb o - twoNormAt starNormPrices n 6 p - twoCornerAt n p o +
    8*scale*(f:Int) = _
  rw [cor]
  unfold twoOrbitStar twoNormAt
  rw [views_sum,views_sum]
  change (∑ g : Fin 8, twoStarBill _ f (rotBits g nb) (turnOut g o)) - _ - _ + _ = _
  simp only [h,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

private theorem patch_remove {n} (F : Finset (GridVertex n n)) (v : origins n) (hn : 2≤n) :
    twoOrbitPatch n (coord v) (maskAt F v) - twoNormAt patchNormPrices (n-2) 5 (coord v) =
    ∑ g, patchMarg F v g := by
  have h (g : Fin 8) :
      twoPatchBill (patchLocation (n-2) (image (n-2) g (coord v))) (rotMask g (maskAt F v)) =
      patchNormPrices.getD (atPos (n-2) 5 (image (n-2) g (coord v))) 0 + patchMarg F v g := by
    unfold twoPatchBill patchMarg
    rw [turn_sum g (twoStripTerm _ _),patchQ_sum g (twoSlotTerm _ _)]
    simp only [patchLocation,twoStripF,twoSlotF]
    ring
  unfold twoOrbitPatch twoNormAt
  rw [views_sum,views_sum,Nat.cast_sub hn]
  simp only [Nat.cast_ofNat,h,sum_add_distrib]; ring

theorem physical_marginals_zero {n : Nat} (hn : 2≤n) (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) :
    twoMarginalSum F P=0 := by
  unfold twoMarginalSum
  simp only [star_remove]
  change (∑ v, ∑ g, starMarg F P v g) +
    (∑ v, (twoOrbitPatch n (coord v) (maskAt F v) - twoNormAt patchNormPrices (n-2) 5 (coord v))) = 0
  simp_rw [patch_remove F _ hn]
  rw [sum_comm, sum_comm (s:=univ (α:=origins n)),←sum_add_distrib]
  apply sum_eq_zero; intro g _
  simp only [starMarg,patchMarg,sum_add_distrib,sum_sub_distrib,twoPortF_zero F P step covers,
    twoStripF_zero hn,twoCoverF_eq_slotF hn,zero_add,zero_sub,add_neg_cancel]

end GridGraphs.ResidueTwoUpper.Stencil
