import GridGraphs.Geometry.PhysicalFaceLine
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset
variable {k : Nat}
abbrev J (k : Nat) := Fin (k+1)
def trans (F : Finset (Site k)) : Finset (Site k) := F.image Prod.swap
@[simp] theorem mem_trans {F : Finset (Site k)} {r c} :
    (r,c) ∈ trans F ↔ (c,r) ∈ F := by simp [trans,Prod.swap_eq_iff_eq_swap]

def L (F : Finset (Site k)) (i j : J k) := letter F (teeth k i) j
private theorem centre (F : Finset (Site k)) (i j : J k) :
    (L F i j).z = decide ((teeth k i,teeth k j)∈F) := by
  simp [L,letter,bit,show 3*j.val<N k from (teeth k j).isLt]; rfl

private theorem witness (F : Finset (Site k)) (i j : J k) (ha : active (L F i j)) :
    ∃ c : Fin (N k), (teeth k i,c)∈F ∧ (c.val+1=3*j.val ∨ 3*j.val+1=c.val) := by
  simp only [L,letter,active,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ha
  rcases ha with ⟨pos,h⟩|h
  · unfold bit at h
    split at h
    · exact ⟨_,of_decide_eq_true h,.inl (by dsimp; omega)⟩
    · contradiction
  · unfold bit at h
    split at h
    · exact ⟨_,of_decide_eq_true h,.inr rfl⟩
    · contradiction

def crossMarks (a b : Letter) := I a.z + I a.l + I a.r + I b.l + I b.r

private theorem price : ∀ a b : Letter, a.z=b.z → ¬(active a ∧ active b) →
    localCredit a + localCredit b + crossMarks a b ≤ 2 := by decide +kernel

theorem local_bound (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic) (i j : J k) :
    localCredit (L F i j) + localCredit (L (trans F) j i) +
      crossMarks (L F i j) (L (trans F) j i) ≤ 2 := by
  apply price
  · simp [centre]
  · rintro ⟨h,v⟩
    obtain ⟨c,hc,dc⟩ := witness F i j h
    obtain ⟨r,hr,dr⟩ := witness (trans F) j i v
    exact CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy
      (teeth k i,c) (r,teeth k j) hc (mem_trans.mp hr) dr.symm dc

def axisDebit (F : Finset (Site k)) : Int :=
  ∑ i : J k, ((run (start (!containsActive (word F (teeth k i)))) (word F (teeth k i))).getD 0 : Nat)
def axisPaths (F : Finset (Site k)) : Int :=
  ∑ i : J k, pathsFrom none (word F (teeth k i))
def axisCredit (F : Finset (Site k)) : Int :=
  ∑ i : J k, ∑ j : J k, localCredit (L F i j)

theorem axis_identity (F : Finset (Site k)) (np : ∀ i, ¬Pitch F (teeth k i)) :
    axisDebit F = axisCredit F + axisPaths F - (k+1:Nat) := by
  have single (i : J k) := physical_line F (teeth k i) (np i)
  unfold axisDebit axisCredit axisPaths
  rw [←sum_add_distrib]
  have one : ((k+1:Nat):Int) = ∑ _ : J k, (1:Int) := by simp
  rw [one,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  obtain ⟨n,h,e⟩ := single i
  rw [h]; simp only [Option.getD_some]
  convert e using 2
  rw [←List.sum_ofFn]
  apply congrArg (· + pathsFrom none (word F (teeth k i)))
  apply congrArg List.sum
  apply List.ext_getElem
  · simp only [word,List.length_ofFn,List.length_map,List.length_range]
  · intro t ht hu
    simp only [word,List.getElem_ofFn,List.getElem_map,List.getElem_range,L]

def crossTotal (F : Finset (Site k)) : Int :=
  ∑ i : J k, ∑ j : J k, crossMarks (L F i j) (L (trans F) j i)

def coarseDeficit (F : Finset (Site k)) : Int :=
  ((k:Int)+1)^2 - axisPaths F - axisPaths (trans F)

theorem paired_budget (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    axisDebit F + axisDebit (trans F) + crossTotal F + coarseDeficit F ≤
      (N k:Int)*(k+1) := by
  have p := sum_le_sum (s:=univ) (fun (i : J k) _ =>
    sum_le_sum (s:=univ) (fun (j : J k) _ => local_bound F acy i j))
  simp only [sum_add_distrib] at p
  rw [sum_comm (f:=fun (i j : J k) => localCredit (L (trans F) j i))] at p
  change axisCredit F + axisCredit (trans F) + crossTotal F ≤ _ at p
  simp at p
  rw [axis_identity F rows,axis_identity _ cols]
  unfold coarseDeficit N
  push_cast at *
  linarith only [p]

end GridGraphs.NoPitch.Budget
