import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarOrientation
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarSink

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7

def starDirs (z : Pos) := (List.range 4).filter fun d => inside 119 (shift z d)

def starMarkVars (p : Offset) (ds : List Nat) :=
  markVar p :: ds.map (fun d => markVar (move p d))

private theorem packVars_map (a : Nat → Bool) (f : Nat → Nat) (xs : List Nat) :
    packVars a (xs.map f)=packVars (a ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [packVars,List.map_cons,Function.comp_apply,ih]

private def starKeep (keep : Fin 4 → Bool) : List Nat :=
  (List.range 4).filter fun d => keep (Fin.ofNat 4 d)

private def paddedMarks (a : Fin 5 → Bool) : Nat → Bool := fun i => a (Fin.ofNat 5 i)

private theorem packed_star_check : ∀ (keep : Fin 4 → Bool) (a : Fin 5 → Bool),
    let ds := starKeep keep
    let m := packVars (paddedMarks a) (0 :: ds.map (·+1))
    bit m 0=(a 0).toNat ∧
    neighbourCode ds m=code (fun d => keep d && a ⟨d.val+1,by omega⟩) := by native_decide

/-- Clipped neighbours are densely packed at the input of the audit;
the expanded four compass slots retain their original direction
numbers, with unrepresented neighbours filled by false. -/
theorem packed_star_bits (a : Nat → Bool) (p : Offset) (z : Pos) :
    let ds := starDirs z
    let m := packVars a (starMarkVars p ds)
    bit m 0=(a (markVar p)).toNat ∧
    neighbourCode ds m=code (fun d : Fin 4 =>
      inside 119 (shift z d) && a (markVar (move p d))) := by
  let keep : Fin 4 → Bool := fun d => inside 119 (shift z d)
  let field : Fin 5 → Bool := fun i =>
    if i.val=0 then a (markVar p) else a (markVar (move p (i.val-1)))
  have dsEq : starKeep keep=starDirs z := by
    unfold starKeep starDirs
    apply List.filter_congr
    intro d hd
    simp [keep,Nat.mod_eq_of_lt (List.mem_range.mp hd)]
  have mEq : packVars (paddedMarks field) (0 :: (starDirs z).map (·+1)) =
      packVars a (starMarkVars p (starDirs z)) := by
    simp only [packVars,starMarkVars,packVars_map]
    have marks : ∀ d∈starDirs z,
        (paddedMarks field ∘ (·+1)) d = (a ∘ fun d => markVar (move p d)) d := by
      intro d hd
      have d4 := List.mem_range.mp (List.mem_filter.mp hd).1
      simp only [paddedMarks,field,Function.comp_apply,Fin.val_ofNat,
        Nat.mod_eq_of_lt (show d+1<5 by omega),show d+1≠0 by omega,if_false,Nat.add_sub_cancel]
    have agree (xs : List Nat) (h : ∀ d∈xs, (paddedMarks field ∘ (·+1)) d =
        (a ∘ fun d => markVar (move p d)) d) :
        packVars (paddedMarks field ∘ (·+1)) xs =
          packVars (a ∘ fun d => markVar (move p d)) xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [packVars,h x (by simp),ih (fun d hd => h d (by simp [hd]))]
    rw [agree _ marks]
    rfl
  have h := packed_star_check keep field
  dsimp only at h ⊢
  rw [dsEq,mEq] at h
  refine ⟨h.1,h.2.trans ?_⟩
  congr 1

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
