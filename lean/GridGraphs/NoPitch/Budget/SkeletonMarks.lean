import GridGraphs.NoPitch.Budget.LinePair

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset
variable {k : Nat}

def owner (x : Fin (N k)) : J k :=
  ⟨(x.val+1)/3,by have := x.isLt; unfold N at this; omega⟩

/-- Each site on the coarse grid lines has one owner and one role:
centre, left, right, up, or down. -/
private def indicator (P : Prop) [Decidable P] : Int := if P then 1 else 0

private theorem slot (F : Finset (Site k)) (r : Fin (N k)) (c : Nat) :
    I (bit F r c) = ∑ x ∈ F, indicator (x.1=r ∧ x.2.val=c) := by
  unfold bit
  split
  next hc =>
    have eq (x : Site k) : (x.1=r ∧ x.2.val=c) ↔ x=(r,⟨c,hc⟩) := by
      simp [Prod.ext_iff,Fin.ext_iff]
    simp_rw [indicator,eq]
    by_cases h : (r,⟨c,hc⟩)∈F <;> simp [I,h]
  next hc =>
    have no (x : Site k) : ¬(x.1=r ∧ x.2.val=c) := by
      have := x.2.isLt; omega
    simp [indicator,no,I]

private def region (x : Site k) (i j : J k) :=
  (x.1.val%3=0 ∨ x.2.val%3=0) ∧ i=owner x.1 ∧ j=owner x.2
private instance (x : Site k) (i j : J k) : Decidable (region x i j) := by
  unfold region; infer_instance

private theorem leftSlot (F : Finset (Site k)) (i j : J k) :
    I (L F i j).l = ∑ x ∈ F, indicator (0<j.val ∧ x.1=teeth k i ∧ x.2.val=3*j.val-1) := by
  by_cases p : 0<j.val
  · simpa [L,letter,p] using slot F (teeth k i) (3*j.val-1)
  · simp [L,letter,p,I,indicator]

private theorem cross_slots (F : Finset (Site k)) (i j : J k) :
    crossMarks (L F i j) (L (trans F) j i) =
      ∑ x ∈ F, indicator (region x i j) := by
  unfold crossMarks
  rw [leftSlot,leftSlot]
  simp only [L,letter,slot,trans,sum_image (fun a _ b _ h => Prod.swap_injective h)]
  simp only [←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  have tooth (a : J k) : (teeth k a).val=3*a.val := rfl
  simp only [indicator,region,owner,Fin.ext_iff,tooth,Prod.swap]
  split_ifs <;> omega

theorem crossTotal_eq (F : Finset (Site k)) :
    crossTotal F = ((skeleton F).card:Int) := by
  simp only [crossTotal,cross_slots]
  conv_lhs =>
    enter [2,i]
    rw [sum_comm]
  rw [sum_comm]
  simp [indicator,region,skeleton,Finset.sum_ite_irrel,ite_and]

theorem physical_mark_budget (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    axisDebit F + axisDebit (trans F) + (F.card:Int) + coarseDeficit F ≤
      (N k:Int)*(k+1) + (F \ skeleton F).card := by
  have h := paired_budget F acy rows cols
  rw [crossTotal_eq] at h
  have part := card_sdiff_add_card_eq_card (s:=skeleton F) (t:=F) (filter_subset ..)
  omega

end GridGraphs.NoPitch.Budget
