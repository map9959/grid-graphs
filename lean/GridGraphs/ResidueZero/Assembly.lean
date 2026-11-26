import GridGraphs.ResidueZero.LocalUpper
import GridGraphs.ResidueZero.PhysicalStar
import GridGraphs.ResidueZero.Six
import GridGraphs.ResidueZero.Nine

namespace GridGraphs.ResidueZero
open Finset

def starTotal {n : Nat} (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) :=
  ∑ v, orbitStar n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v))

def patchTotal {n : Nat} (F : Finset (GridVertex n n)) :=
  ∑ p : GridVertex (n-2) (n-2), orbitPatch n (p.1.val,p.2.val)
    (physicalMask F p.1 p.2 (by have := p.1.isLt; omega) (by have := p.2.isLt; omega))

def cornerSite (k : Nat) (hk : 4≤k) : GridVertex (3*k) (3*k) := (⟨0,by omega⟩,⟨0,by omega⟩)

/-- The outstanding physical double counting: sum the opposite endpoint
charges for star/edge, star/patch and patch/patch incidences. Only the
nonpositive corner-root price can leave an inequality. -/
def PhysicalCancellation (k : Nat) (hk : 4≤k) : Prop :=
  ∀ (F : Finset (GridVertex (3*k) (3*k))) (P : GridVertex (3*k) (3*k) → GridVertex (3*k) (3*k)),
    (Bonds F).IsAcyclic → P (cornerSite k hk)=cornerSite k hk →
    (∀ v, P v≠v → (Bonds F).Adj v (P v)) →
    (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) →
    starTotal F P + patchTotal F + 8*scale*(F.card:Int) ≤ 8*normBudget (3*k)

theorem physicalTotals_nonneg {k : Nat} (hk : 4≤k) (F : Finset (GridVertex (3*k) (3*k)))
    (acy : (Bonds F).IsAcyclic) (P : GridVertex (3*k) (3*k) → GridVertex (3*k) (3*k))
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v)) :
    0 ≤ starTotal F P ∧ 0 ≤ patchTotal F := by
  constructor
  · apply sum_nonneg; intro v _
    exact star_nonneg hk (coord_inside _) (by cases decide (v∈F) <;> decide)
      (code_lt _) (outDir_lt ..) (starOK_physical F acy v _ (fun h => step _ h.symm))
  · apply sum_nonneg; intro p _
    exact physicalPatch_nonneg hk F acy _ _ _ _

theorem exact_of_cancellation {k : Nat} (hk : 4≤k) (cancel : PhysicalCancellation k hk) :
    maxPreserved (3*k) (3*k) = squareScore (3*k) := by
  apply le_antisymm _ (squareScore_lower_three_mul k (by omega))
  by_contra! above
  obtain ⟨F,hF,card⟩ := (squareMaskScore_iff_le (s:=squareScore (3*k)+1) (by omega : 0<3*k)).mpr above
  have forest := mem_acyclicForcedSets.mp hF
  obtain ⟨P,root,step,covers⟩ := parent_exists F (cornerSite k hk) forest
  obtain ⟨st,pt⟩ := physicalTotals_nonneg hk F forest P step
  have bound := cancel F P forest root step covers
  rw [budget_eq_score hk,card] at bound
  simp [scale] at bound
  omega

theorem exact_all_of_cancellation
    (cancel : ∀ k (hk : 4≤k), PhysicalCancellation k hk) {k : Nat} (hk : 1≤k) :
    maxPreserved (3*k) (3*k) = 3*k^2+3*k-2 := by
  rw [← squareScore_three_mul]
  by_cases h : 4≤k
  · exact exact_of_cancellation h (cancel k h)
  · interval_cases k
    · exact maxPreserved_three_three
    · exact maxPreserved_six
    · exact Nine.maximum_eq

end GridGraphs.ResidueZero
