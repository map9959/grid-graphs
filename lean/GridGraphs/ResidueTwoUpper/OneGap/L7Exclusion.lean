import GridGraphs.ResidueTwoUpper.OneGap.L7Physical
import GridGraphs.ResidueTwoUpper.OneGap.L7Rim
import GridGraphs.Tests.OneGapL7Scan
import GridGraphs.Tests.OneGapL7Catalogue
import GridGraphs.ResidueTwoUpper.OneGap.DefectSites

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
open ResidueZero Stencil GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected

private theorem label_seven (s : Bool) (X : Nat → Nat) (n : Nat) :
    label s X (7+n)=label s X 7 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ j ∈ Finset.range ((7+n)+1),observe s j (X j))=_
    rw [Finset.sum_range_succ]
    change label s X (7+n)+observe s (7+n) (X (7+n))=_
    simp [ih,observe,show 7+n≠2 by omega,show 7+n≠3 by omega,show 7+n≠4 by omega,
      show 7+n≠5 by omega,show 7+n≠6 by omega]

private theorem shared {n} (F : Finset (GridVertex n n)) (v : View) :
    label false (chartCol F v) 7=label true (chartCol F (turnView v)) 7 := by
  have cb (w : View) (i : Nat) (h : i<7) (j : Nat) := col_bit F w ⟨i,h⟩ j
  simp [label,Finset.sum_range_succ,observe,cb,turned,Nat.add_assoc]

theorem column_of_rim {n} (F : Finset (GridVertex n n)) (v : View) (s f : Bool)
    (h : rim F v s f) (j : Nat) (hj : j<n) : columnOK n s f j (chartCol F v j) := by
  apply List.all_eq_true.mpr
  intro r hr
  have hr := List.mem_range.mp hr
  cases e : preset n s f r j with
  | none => simp
  | some b =>
    have z := (col_bit F v ⟨r,hr⟩ j).trans (congrArg Bool.toNat (h r j hr hj b e))
    simp [z]

/-- Both arms use marks of the same forest at their shared junction. -/
theorem junction_false (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (v : View) (f g : Bool) (h : rim F v false f) (k : rim F (turnView v) true g)
    (localOK : ∀ w, w=v ∨ w=turnView v → ∀ j<33+42*u,
      band (fold u j) (chartCol F w j) (chartCol F w (j+1)) (chartCol F w (j+2))) : False := by
  have cert (s t) : midOK s t=true ∧ outputOK s t=true := by simpa using scan_checked s t
  have run (w s t) (side : w=v ∨ w=turnView v) (r : rim F w s t) := scan_sound u s t (chartCol F w) (col_lt F w)
    (column_of_rim F w s t r) (localOK w side)
    (cert s t).1 (cert s t).2
  have A := run _ _ _ (.inl rfl) h
  have B := run _ _ _ (.inr rfl) k
  have seven (s X) : label s X (35+42*u)=label s X 7 := by
    rw [show 35+42*u=7+(28+42*u) by omega,label_seven]
  rw [seven,shared] at A
  rw [seven] at B
  simp at A B
  omega

/-- On all sides 35+42u, including 35 and 77, the one-gap frame cannot have
zero stars and patches of charge zero or full. No restriction on the
location or visibility of the charged patch is needed. -/
theorem patch_impossible (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (P : GridVertex (35+42*u) (35+42*u) → _)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (good : ∀ x, allGood F P x)
    (zs : ∀ x, starSlack F P x=0) (wp : ∀ a, patchSlack F a=0 ∨ patchSlack F a=full) : False := by
  have hn : 35≤35+42*u := by omega
  have geo (x) := star_geometry hn F P step x (good (.inl x))
  obtain ⟨v,f,g,h,k⟩ := pair_rim hn F (corners_marked u F acy score)
    (fun x => (geo x).1) (fun x => (geo x).2.1) (TwoGap.Words.physicalWord_ok hn F P good) one
  exact junction_false u F v f g h k (fun w _ => physical_band catalogue_checked u F acy P step zs wp w)

/-- The patch alternative of `defect_sites` is eliminated at every origin. -/
theorem isolated_star_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (v : GridVertex n n),
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧ (∀ x, allGood F P x) ∧
      (Bonds F).IsIsolated v ∧ (arm n (coord v).1 (coord v).2 ∨ arm n (coord v).2 (coord v).1) ∧
      starSlack F P v=full ∧ ∀ x, x≠Sum.inl v → weightAt F P x=0 := by
  obtain ⟨P,step,arr,good,stars|patch⟩ := defect_sites u F acy score one
  · obtain ⟨v,h⟩ := stars
    exact ⟨P,v,step,arr,good,h⟩
  · obtain ⟨a,_,_,paid,zero⟩ := patch
    apply False.elim (patch_impossible u F acy score one P step good
      (fun v => zero (.inl v) (by simp)) _)
    intro b
    by_cases h : b=a
    · exact Or.inr (h ▸ paid)
    · exact Or.inl (zero (.inr b) (by simpa using h))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
