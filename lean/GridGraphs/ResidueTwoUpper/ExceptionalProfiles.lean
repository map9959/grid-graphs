import GridGraphs.ResidueTwoUpper.ExceptionalPropagation

/-! The surviving unordered charge profiles are the singleton full defect
and a pair of distinct half defects. There is no symmetry assumption on
the physical mark set. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil Finset

instance (n : Nat) : Fintype (occurrence n) := inferInstanceAs (Fintype (_ ⊕ _))

theorem profile_counts {I : Type*} [Fintype I] (w : I → Int)
    (good : ∀ i, weights (w i)) (total : ∑ i, w i=full) :
    let count := fun a => (univ.filter (fun i => w i=a)).card
    count threeQuarters=0 ∧
      ((count half=0 ∧ count full=1) ∨ (count half=2 ∧ count full=0)) := by
  classical
  let indicator (a : Int) (i : I) : Int := if w i=a then 1 else 0
  have decomp (i : I) : w i=half*indicator half i+threeQuarters*indicator threeQuarters i+full*indicator full i := by
    have h := good i
    simp only [weights,Bool.or_eq_true,beq_iff_eq] at h
    rcases h with ((h|h)|h)|h <;> simp [indicator,h,half,threeQuarters,full]
  have counts (a : Int) : ∑ i, indicator a i=((univ.filter fun i => w i=a).card:Int) := by
    simp [indicator]
  have eq := sum_congr (s₁:=univ) rfl (fun i _ => decomp i)
  rw [total] at eq
  simp only [sum_add_distrib,←mul_sum,counts] at eq
  dsimp only
  unfold half threeQuarters full at eq ⊢
  omega

theorem surviving_profiles (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    let n := 35+42*u
    let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
    ∃ P : GridVertex n n → GridVertex n n, P root=root ∧
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      (∀ x, isCorner x → P x=x → x=root) ∧
      let w := weightAt F P
      let count := fun a => (univ.filter (fun x => w x=a)).card
      (∀ x, w x=0 ∨ w x=half ∨ w x=full) ∧
        ((count half=0 ∧ count full=1) ∨ (count half=2 ∧ count full=0)) := by
  dsimp only
  obtain ⟨P,sink,step,covers,_,corners,total⟩ := exceptional_slack u F acy score
  have good := physical_weights checked_stars checked_patches u F P acy step total
  have all : (∑ x, weightAt F P x)=full := by
    exact (Fintype.sum_sum_type (Sum.elim (starSlack F P) (patchSlack F))).trans total
  obtain ⟨no,counts⟩ := profile_counts _ good all
  refine ⟨P,sink,step,covers,corners,?_,counts⟩
  intro x
  have ok := good x
  simp only [weights,Bool.or_eq_true,beq_iff_eq] at ok
  rcases ok with ((h|h)|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact False.elim ((Finset.card_ne_zero_of_mem (mem_filter.mpr ⟨mem_univ x,h⟩)) no)
  · exact Or.inr (Or.inr h)

end GridGraphs.ResidueTwoUpper.Exceptional
