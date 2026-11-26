import GridGraphs.Tests.ElevenPriceReplay
import GridGraphs.Constructions.Finite.FiniteDiagonalEleven

/-! Side eleven. Local replay checks a finite list of star configurations
and 3×3 patch masks, never complete forests. -/
namespace GridGraphs
open ResidueZero hiding scale

theorem maxPreserved_eleven_upper : maxPreserved 11 11 ≤ 49 := by
  obtain ⟨F,hF,num⟩ := (squareMaskScore_iff_le (n:=11) (by decide)).mpr
    (le_refl (maxPreserved 11 11))
  have h := Eleven.physical_budget (by decide) F (mem_acyclicForcedSets.mp hF)
    (fun _ _ _ _ hp hf hn ho ok => Eleven.fromStar Eleven.checkedStars hp hf hn ho ok)
    (fun _ _ hp hm ok => Eleven.fromPatch Eleven.checkedPatches hp hm ok)
  rw [Eleven.checkedBudget] at h
  change 100000*(F.card:Int) ≤ 4922020 at h
  omega

theorem maxPreserved_eleven_eleven : maxPreserved 11 11 = 49 :=
  Nat.le_antisymm maxPreserved_eleven_upper fortyNine_le_maxPreserved_eleven_eleven

end GridGraphs
