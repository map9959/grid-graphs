import GridGraphs.Geometry.PhysicalFaceLine
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace GridGraphs.NoPitch
open Finset MulAction PitchCut

abbrev SquareSym := DihedralGroup 4

/-! Canonical star variables store one count per oriented member of an
orbit. A site contributes the stabilizer order to its variable; a marked
star orbit has objective coefficient equal to its number of members. -/
variable {A : Type*} [MulAction SquareSym A] [Finite A]

noncomputable def multiplicity (a : A) := Nat.card (stabilizer SquareSym a)
noncomputable def orbitWeight (a : A) := Nat.card (orbit SquareSym a)

theorem orbit_units (a : A) : orbitWeight a * multiplicity a=8 := by
  classical
  let _ := Fintype.ofFinite ↥(orbit SquareSym a)
  let _ := Fintype.ofFinite ↥(stabilizer SquareSym a)
  simpa only [orbitWeight,multiplicity,Nat.card_eq_fintype_card,DihedralGroup.card] using
    card_orbit_mul_card_stabilizer_eq_card_group SquareSym a

/-- Group by the actual orbit and centre mark together. The coefficient
for an orbit is its cardinality, so symmetric stars are not overcounted. -/
noncomputable def starCounts {k : Nat} (F : Finset (Site k)) (atom : Site k → A)
    (key : Bool × Set A) : Nat := by
  classical
  exact ∑ x : Site k, if (decide (x∈F),orbit SquareSym (atom x))=key then
    multiplicity (atom x) else 0

theorem physical_star_objective {k : Nat} (F : Finset (Site k)) (atom : Site k → A) :
    ∑ key ∈ (univ.image (fun x : Site k => (decide (x∈F),orbit SquareSym (atom x))) :
        Finset (Bool × Set A)),
      (if key.1 then Nat.card key.2 else 0)*starCounts F atom key = 8*F.card := by
  classical
  let tag (x : Site k) := (decide (x∈F),orbit SquareSym (atom x))
  change (∑ key ∈ univ.image tag, _)=_
  simp only [starCounts,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ x : Site k, if x∈F then 8 else 0 := by
      apply sum_congr rfl; intro x _
      rw [sum_eq_single (tag x)]
      · by_cases m : x∈F <;> simp [tag,m]
        exact orbit_units (atom x)
      · intro b _ ne
        simp [show (decide (x∈F),orbit SquareSym (atom x))≠b from Ne.symm ne]
      · simp [mem_image_of_mem tag (mem_univ x)]
    _ = _ := by simp [mul_comm]

end GridGraphs.NoPitch
