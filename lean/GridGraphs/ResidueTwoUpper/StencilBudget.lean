import GridGraphs.ResidueTwoUpper.StencilPrices
import GridGraphs.ResidueZero.Budget

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

private theorem plane_width {b d : Nat} (hb : 19≤b) (hd : 5≤d ∧ d≤6)
    (f : Int → Int → Int) (j : Nat) :
    plane (b+3*j) d f = plane b d f +
      j*(axisSum b d (fun i => extra d (f i)) + extra d (fun i => axisSum b d (f i))) +
      (j:Int)^2*extra d (fun i => extra d (f i)) := by
  unfold plane
  simp_rw [axisSum_width hb hd]
  simp only [axisSum,extra,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

private def linear (b d : Nat) (f : Int → Int → Int) :=
  axisSum b d (fun i => extra d (f i)) + extra d (fun i => axisSum b d (f i))
private def quadratic (d : Nat) (f : Int → Int → Int) := extra d (fun i => extra d (f i))

def rhs (n : Nat) := plane n 6 (charge starNormPrices) + plane (n-2) 5 (charge patchNormPrices) + cornerPrices.getD 0 0

theorem budget (t : Nat) : 14*rhs (20+3*t) = scale*(2111+600*(t:Int)+42*(t:Int)^2) := by
  cases t with
  | zero => native_decide
  | succ j =>
    have c₀ : 14*rhs 23 = scale*2753 := by native_decide
    have c₁ : 14*(linear 23 6 (charge starNormPrices)+linear 21 5 (charge patchNormPrices)) = scale*684 := by native_decide
    have c₂ : 14*(quadratic 6 (charge starNormPrices)+quadratic 5 (charge patchNormPrices)) = scale*42 := by native_decide
    rw [show 20+3*(j+1)=23+3*j by omega]
    unfold rhs at c₀ ⊢
    rw [show 23+3*j-2=21+3*j by omega,plane_width (by decide) (by decide),plane_width (by decide) (by decide)]
    unfold linear at c₁; unfold quadratic at c₂
    push_cast
    linear_combination c₀ + (j:Int)*c₁ + (j:Int)^2*c₂

end GridGraphs.ResidueTwoUpper.Stencil
