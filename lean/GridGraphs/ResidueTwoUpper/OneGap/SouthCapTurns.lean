import GridGraphs.ResidueTwoUpper.OneGap.SouthCapHaloPrices

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

private noncomputable def sheetOf {V : Type*} (parent : V → V) (rank : V → Nat)
    (down : ∀ x, parent x ≠ x → rank (parent x) < rank x) (turn : V → Bool) (x : V) : Bool := by
  classical
  exact if h : parent x ≠ x then xor (sheetOf parent rank down turn (parent x)) (turn x) else false
termination_by rank x
decreasing_by exact down x h

/-- Construct sheets for the catalogue's compass convention directly.
This works after swapping or reflecting the view: the turn test need
not agree with the wrap test in the original physical compass. The
result is a single function on vertices, not a choice per halo. -/
theorem parent_sheet {V : Type*} (parent : V → V) (rank : V → Nat)
    (down : ∀ x, parent x ≠ x → rank (parent x) < rank x)
    (turn : V → Bool) :
    ∃ sheet : V → Bool, ∀ x, parent x ≠ x →
      sheet (parent x) = xor (sheet x) (turn x) := by
  refine ⟨sheetOf parent rank down turn, ?_⟩
  intro x hx
  conv_rhs =>
    arg 1
    rw [sheetOf, dif_pos hx]
  cases sheetOf parent rank down turn (parent x) <;> cases turn x <;> rfl

/-- In particular every pair of successive nonstationary parents
obeys the two-sheet rule in any compass used to name their directions. -/
theorem compass_sheet {V : Type*} (parent : V → V) (rank : V → Nat)
    (down : ∀ x, parent x ≠ x → rank (parent x) < rank x)
    (dir : V → V → Nat) :
    ∃ sheet : V → Bool, ∀ x y z, parent x=y → x≠y → parent y=z → y≠z →
      sheet y=xor (sheet x) (decide
        ((dir x y=0 ∧ dir y z=3) ∨ (dir x y=3 ∧ dir y z=0))) := by
  obtain ⟨sheet, hs⟩ := parent_sheet parent rank down (fun x =>
    decide ((dir x (parent x)=0 ∧ dir (parent x) (parent (parent x))=3) ∨
      (dir x (parent x)=3 ∧ dir (parent x) (parent (parent x))=0)))
  refine ⟨sheet, fun x y z xy ne yz _ => ?_⟩
  have h := hs x (by simpa [xy] using ne.symm)
  rw [xy,yz] at h
  exact h

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
