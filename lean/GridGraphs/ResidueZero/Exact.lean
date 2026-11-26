import GridGraphs.ResidueZero.Balance
import GridGraphs.ResidueZero.PhysicalSum

/-! End-to-end upper certificate and exact value for positive multiples of three. -/
namespace GridGraphs.ResidueZero
open Finset

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
  (∑ d ∈ range 4, portF F P g v d) + ∑ q : Fin 9, coverF F g v q
private def patchMarg {n} (F : Finset (GridVertex n n)) (v : origins n) (g : Fin 8) :=
  (∑ d ∈ range 4, stripF F g v d) - ∑ q : Fin 9, slotF F g v q

private theorem star_remove {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (v : GridVertex n n) :
    orbitStar n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v)) -
    normAt starNormPrices n 6 (coord v) - cornerAt n (coord v) (outDir v (P v)) +
    8*scale*((decide (v∈F)).toNat:Int) = ∑ g, starMarg F P v g := by
  let f := (decide (v∈F)).toNat
  let o := outDir v (P v)
  let p := coord v
  let nb := neighbours F p
  let c (g : Fin 8) := if o=4 then 4*cornerPrices.getD (atPos n 6 (image n g p)) 0 else 0
  have cor : cornerAt n p o = ∑ g, c g := by
    unfold cornerAt; by_cases h : o=4 <;> simp [h,c,views_sum]
  have h (g : Fin 8) :
      starBill (starLocation n (image n g p)) f (rotBits g nb) (turnOut g o) =
        starNormPrices.getD (atPos n 6 (image n g p)) 0 - scale*(f:Int) +
          c g + starMarg F P v g := by
    have oo : turnOut g o=4 ↔ o=4 := by
      by_cases ho : o=4
      · simp [ho,turnOut]
      · have lt : turn g o < 4 := Nat.mod_lt _ (by decide)
        simp [turnOut,ho,show turn g o ≠ 4 by omega]
    unfold starBill starMarg
    rw [turn_sum g (port _ _ _ _),patchQ_sum g (coverTerm _ _ _)]
    simp only [starLocation,oo,c,portF,coverF,nb,p,f,o,add_assoc]
  change orbitStar n p f nb o - normAt starNormPrices n 6 p - cornerAt n p o +
    8*scale*(f:Int) = _
  rw [cor]
  unfold orbitStar normAt
  rw [views_sum,views_sum]
  change (∑ g : Fin 8, starBill _ f (rotBits g nb) (turnOut g o)) - _ - _ + _ = _
  simp only [h,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

private theorem patch_remove {n} (F : Finset (GridVertex n n)) (v : origins n) (hn : 2≤n) :
    orbitPatch n (coord v) (maskAt F v) - normAt patchNormPrices (n-2) 5 (coord v) =
    ∑ g, patchMarg F v g := by
  have h (g : Fin 8) :
      patchBill (patchLocation (n-2) (image (n-2) g (coord v))) (rotMask g (maskAt F v)) =
      patchNormPrices.getD (atPos (n-2) 5 (image (n-2) g (coord v))) 0 + patchMarg F v g := by
    unfold patchBill patchMarg
    rw [turn_sum g (stripTerm _ _),patchQ_sum g (slotTerm _ _)]
    simp only [patchLocation,stripF,slotF]
    ring
  unfold orbitPatch normAt
  rw [views_sum,views_sum,Nat.cast_sub hn]
  simp only [Nat.cast_ofNat,h,sum_add_distrib]; ring

theorem physical_marginals_zero {n : Nat} (hn : 2≤n) (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) :
    marginalSum F P=0 := by
  unfold marginalSum
  simp only [star_remove]
  change (∑ v, ∑ g, starMarg F P v g) +
    (∑ v, (orbitPatch n (coord v) (maskAt F v) - normAt patchNormPrices (n-2) 5 (coord v))) = 0
  simp_rw [patch_remove F _ hn]
  rw [sum_comm, sum_comm (s:=univ (α:=origins n)),←sum_add_distrib]
  apply sum_eq_zero; intro g _
  simp only [starMarg,patchMarg,sum_add_distrib,sum_sub_distrib,portF_zero F P step covers,
    stripF_zero hn,coverF_eq_slotF hn,zero_add,zero_sub,add_neg_cancel]

/-- The unrestricted graph-theoretic equality, with no width, waste,
pitch, maximal-mask, or physical-feasibility assumptions beyond `1 ≤ k`. -/
theorem maxPreserved_three_mul {k : Nat} (hk : 1≤k) :
    maxPreserved (3*k) (3*k) = 3*k^2+3*k-2 :=
  exact_all_of_cancellation (fun _ h =>
    cancellation_of_marginals h (fun F P _ _ step covers =>
      physical_marginals_zero (by omega) F P step covers)) hk

end GridGraphs.ResidueZero
