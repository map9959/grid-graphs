import GridGraphs.ResidueZero.Assembly
import GridGraphs.ResidueZero.Normalization

/-! After stripping the verified prices for normalization, corner roots
and marked centres, only the signed marginal charges remain. -/
namespace GridGraphs.ResidueZero
open Finset

def normAt (tab : Std.HashMap Nat Int) (s d : Nat) (p : Pos) :=
  ((List.range 8).map fun g => tab.getD (atPos s d (image s g p)) 0).sum

def cornerAt (n : Nat) (p : Pos) (o : Nat) :=
  if o=4 then ((List.range 8).map fun g => 4*cornerPrices.getD (atPos n 6 (image n g p)) 0).sum
  else 0

theorem normAt_sum (s d : Nat) (tab : Std.HashMap Nat Int) :
    (∑ v : GridVertex s s, normAt tab s d (coord v)) = 8*plane s d (charge tab) := by
  simp [normAt,show List.range 8=[0,1,2,3,4,5,6,7] by decide,sum_add_distrib,sum_norm_image]
  ring

private theorem cornerAt_nonpos (n : Nat) (p : Pos) (o : Nat) : cornerAt n p o ≤ 0 := by
  have le (g : Nat) := corner_nonpos n (image n g p) 4
  simp at le
  simp only [cornerAt,show List.range 8=[0,1,2,3,4,5,6,7] by decide,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  split_ifs <;> linarith [le 0,le 1,le 2,le 3,le 4,le 5,le 6,le 7]

theorem sum_corner {k : Nat} (hk : 4≤k) (P : GridVertex (3*k) (3*k) → GridVertex (3*k) (3*k))
    (root : P (cornerSite k hk)=cornerSite k hk) :
    (∑ v, cornerAt (3*k) (coord v) (outDir v (P v))) ≤ 8*cornerPrices.getD 0 0 := by
  let c := cornerSite k hk
  have cut := Finset.sum_erase_add (s:=(univ : Finset (GridVertex (3*k) (3*k)))) (mem_univ c)
    (f:=fun v => cornerAt (3*k) (coord v) (outDir v (P v)))
  have nonpos := Finset.sum_nonpos (s:=univ.erase c) (fun v _ => cornerAt_nonpos (3*k) (coord v) (outDir v (P v)))
  have root' : P c=c := root
  have rootbill : cornerAt (3*k) (coord c) (outDir c (P c))=8*cornerPrices.getD 0 0 := by
    rw [root']; simpa [outDir,cornerAt,coord,c,cornerSite] using root_corner_sum (n:=3*k) (by omega)
  linarith

/-- Net signed marginal prices, obtained by removing all other terms
from each checked eight-view charge. The sign convention matches `starBill`
and `patchBill` (edge first minus second; incidence star minus patch). -/
def marginalSum {n : Nat} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) :=
  (∑ v, (orbitStar n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v)) -
    normAt starNormPrices n 6 (coord v) - cornerAt n (coord v) (outDir v (P v)) +
    8*scale*((decide (v∈F)).toNat:Int))) +
  ∑ p : GridVertex (n-2) (n-2), (orbitPatch n (coord p)
    (physicalMask F p.1 p.2 (by have := p.1.isLt; omega) (by have := p.2.isLt; omega)) -
    normAt patchNormPrices (n-2) 5 (coord p))

theorem cancellation_of_marginals {k : Nat} (hk : 4≤k)
    (bal : ∀ (F : Finset (GridVertex (3*k) (3*k))) (P : GridVertex (3*k) (3*k) → GridVertex (3*k) (3*k)),
      (Bonds F).IsAcyclic → P (cornerSite k hk)=cornerSite k hk →
      (∀ v, P v≠v → (Bonds F).Adj v (P v)) →
      (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) → marginalSum F P=0) :
    PhysicalCancellation k hk := by
  intro F P acy root step covers
  have h := bal F P acy root step covers
  simp only [marginalSum,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_mark,normAt_sum] at h
  change starTotal F P - _ - _ + _ + (patchTotal F - _) = 0 at h
  unfold normBudget
  linarith [sum_corner hk P root]

end GridGraphs.ResidueZero
