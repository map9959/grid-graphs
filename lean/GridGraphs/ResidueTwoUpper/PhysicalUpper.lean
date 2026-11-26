import GridGraphs.ResidueTwoUpper.DecodedNormalization
import GridGraphs.ResidueTwoUpper.Overlap

namespace GridGraphs.ResidueTwoUpper.PhysicalUpper
open Finset PhysicalCounts NoPitch.Dual DecodedNormalization GridGraphs.ResidueTwoUpper.Star

def base (d z : Nat) := Normalization.axisMass d 0 z
def gain (d z : Nat) : Int := if d≤z ∧ z<d+3 then 1 else 0
private theorem affine (d t z : Nat) :
    Normalization.axisMass d t z=base d z+gain d z*t := by
  unfold base gain Normalization.axisMass
  split_ifs <;> omega

def normalRhs (i : Fin 38) : Poly :=
  let d := dp i
  let a := tag i/16
  let b := tag i%16
  ⟨2*base d a*base d b,2*(base d a*gain d b+gain d a*base d b),2*gain d a*gain d b⟩

theorem normalRhs_eq (i : Fin 38) (t : Nat) : (normalRhs i).atStep t=2*mass i t := by
  simp only [normalRhs,Poly.atStep,mass,affine]
  ring

theorem metadata : ∀ (i : Fin 38), ∃ h : i.val<periodThree.rows.size,
    if i.val=1 then periodThree.rows[i.val].sense=2 ∧ periodThree.rows[i.val].rhs=⟨2,0,0⟩
    else periodThree.rows[i.val].sense=0 ∧ periodThree.rows[i.val].rhs=normalRhs i := by
  native_decide

private theorem root_code (t) (F : Finset (Site (N t))) (ac : (Forced F).IsAcyclic) :
    starKey F ac (root t)/2%5=0 := by
  let x := root t
  have sink : out (arrows F ac) x=none := (out_none _ _).mpr (arrows F ac).sink
  change key _ _ _ _ _ (out (arrows F ac) x)/2%5=0
  rw [sink]
  obtain ⟨g,e⟩ := min_view (encoding (N t) x.1 x.2 (decide (x∈F))
    (letter (N t) x.1 x.2 (sample F x)) none)
  unfold key; rw [e]; simp [encoding]

private theorem contribution_nonneg (i : Fin 38) (k : Nat) : 0≤contribution i k := by
  have un (d a b z : Nat) : 0≤Views.units d a b z := Finset.sum_nonneg fun _ _ => by split_ifs <;> decide
  unfold contribution; split_ifs <;> first | exact le_refl 0 | exact un .. | exact mul_nonneg (by decide) (un ..)

theorem corner_lower {t} (F : Finset (Site (N t))) (ac : (Forced F).IsAcyclic)
    (j : Fin periodThree.rows.size) (one : j.val=1) :
    8 ≤ lhs periodThree (vector F ac) j := by
  rw [decompose F ac 1 j one]
  let f := fun x => contribution 1 (starKey F ac x)
  have rootUnits : tally 6 (root t) 0=2 := by
    have a : Location.axis (N t) 6 0=0 := rfl
    change Views.units 6 (Location.axis (N t) 6 0) (Location.axis (N t) 6 0) 0=2
    rw [a]; decide
  have rootBill : f (root t)=8 := by
    have u := star_units F ac (root t) 1
    change _=tally 6 (root t) 0 at u
    rw [show tag 1=0 by decide,rootUnits] at u
    simp [f,contribution,key_even F ac,root_code,dp,show tag 1=0 by decide,u]
  have nonneg (x) : 0≤f x := by
    exact contribution_nonneg .. 
  have le := Finset.single_le_sum (s:=univ) (f:=f) (fun x _ => nonneg x) (mem_univ (root t))
  have skip (x : Site (S t)) : contribution 1 (patchKey F x)=0 := by
    simp [contribution,key_odd]
  simpa only [skip,sum_const_zero,add_zero,rootBill] using le

attribute [local irreducible] periodThree

theorem bound_of_remaining {t} (F : Finset (Site (N t))) (ac : (Forced F).IsAcyclic)
    (rows : ∀ j : Fin periodThree.rows.size, 38≤j.val →
      rowHolds periodThree.rows[j].sense (2*lhs periodThree (vector F ac) j)
        (8*periodThree.rows[j].rhs.atStep t)) :
    14*(F.card:Int) ≤ 2111+600*(t:Int)+42*(t:Int)^2 := by
  apply rational_upper (x:=vector F ac) (cap:=0) _ (objective F ac)
  constructor
  · exact nonnegative F ac
  · have check : periodThree.cols.all (fun c => !c.fixed) := by native_decide
    intro j fixed
    have no := Array.all_eq_true_iff_forall_mem.mp check _ (Array.getElem_mem j.isLt)
    change (!periodThree.cols[j].fixed)=true at no
    have bad : true=false := fixed.symm.trans (by simpa only [Bool.not_eq_true'] using no)
    exact False.elim (Bool.noConfusion bad)
  · have zero : ∀ j, price periodThree j ≤ 0 := by native_decide
    intro j bad; exact False.elim ((zero j).not_gt bad)
  · intro (j : Fin periodThree.rows.size)
    classical
    apply (Nat.lt_or_ge (Fin.val j) 38).elim
    · intro hi
      let i : Fin 38 := ⟨j.val,hi⟩
      obtain ⟨_,eq⟩ := metadata i
      by_cases one : i.val=1
      · rw [if_pos one] at eq
        have c := corner_lower F ac j one
        change periodThree.rows[j].sense=2 ∧ periodThree.rows[j].rhs=_ at eq
        rw [eq.1,eq.2]; norm_num [rowHolds,Poly.atStep]; omega
      · rw [if_neg one] at eq
        change periodThree.rows[j].sense=0 ∧ periodThree.rows[j].rhs=normalRhs i at eq
        rw [eq.1,eq.2,normalized F ac i j rfl one,normalRhs_eq]
        simp [rowHolds]; ring
    · exact rows j

end GridGraphs.ResidueTwoUpper.PhysicalUpper
