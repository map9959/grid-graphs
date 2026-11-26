import GridGraphs.ResidueTwoUpper.StencilAssembly
import GridGraphs.ResidueTwoUpper.StencilReplay

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero

theorem physical_rational_upper (t : Nat) (F : Finset (GridVertex (20+3*t) (20+3*t)))
    (acy : (Bonds F).IsAcyclic) : 14*(F.card:Int) ≤ 2111+600*(t:Int)+42*(t:Int)^2 :=
  physical_upper_of_checks checkStars checkPatches t F acy

theorem maxPreserved_period_three {k : Nat} (hk : 6 ≤ k) :
    maxPreserved (3*k+2) (3*k+2) ≤ 3*k^2+7*k-(k-5)/7 := by
  let t := k-6
  have e : 3*k+2=20+3*t := by dsimp [t]; omega
  obtain ⟨F,hF,sc⟩ := (squareMaskScore_iff_le (n:=20+3*t) (by omega)).mpr
    (le_refl (maxPreserved (20+3*t) (20+3*t)))
  rw [e,←sc]
  have h := physical_rational_upper t F (mem_acyclicForcedSets.mp hF)
  have et : (t:Int)=(k:Int)-6 := by dsimp [t]; omega
  rw [et] at h; ring_nf at h
  have dv : 7*((((k-5)/7 : Nat):Int)) ≤ (k:Int)-5 := by omega
  have b : (F.card:Int)+((k-5)/7 : Nat) ≤ 3*(k:Int)^2+7*k := by omega
  have bn : F.card+(k-5)/7 ≤ 3*k^2+7*k := by exact_mod_cast b
  omega

/-- Thirteen of fourteen parameter classes need no further upper argument. -/
theorem maxPreserved_le_squareScore {k : Nat} (hk : 6 ≤ k) (ordinary : k%14≠11) :
    maxPreserved (3*k+2) (3*k+2) ≤ squareScore (3*k+2) := by
  simpa only [squareScore_three_mul_add_two k hk,if_neg ordinary,Nat.sub_zero]
    using maxPreserved_period_three hk

/-- On the exceptional progression, the remaining upper-side obligation
is exclusion of exactly one score. -/
theorem maxPreserved_le_squareScore_succ {k : Nat} (hk : 6 ≤ k) :
    maxPreserved (3*k+2) (3*k+2) ≤ squareScore (3*k+2)+1 := by
  have h := maxPreserved_period_three hk
  rw [squareScore_three_mul_add_two k hk]
  split_ifs <;> omega

theorem below_old_target {k : Nat} (hk : 12 ≤ k) :
    maxPreserved (3*k+2) (3*k+2) < 3*k^2+7*k := by
  have h := maxPreserved_period_three (k:=k) (by omega)
  have pos : 0<3*k^2+7*k := by positivity
  omega

theorem twenty_exact : maxPreserved 20 20=150 :=
  le_antisymm (maxPreserved_period_three (k:=6) (by decide)) oneHundredFifty_le_maxPreserved_twenty_twenty

end GridGraphs.ResidueTwoUpper.Stencil
