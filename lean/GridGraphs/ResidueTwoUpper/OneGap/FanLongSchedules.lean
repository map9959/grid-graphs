import GridGraphs.ResidueTwoUpper.OneGap.SpeedCover

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed

private def iter (k q : Nat) : Nat → State → Bool
  | 0,p => decide (cap k p)
  | a+1,p => decide (cap k p) || moves.any fun m => decide (fits k q m p) && iter k q a (next m q p)
private theorem iter_sound {k q a p} (h : iter k q a p) : Reaches k q p := by
  induction a generalizing p with
  | zero => exact .capEnd p (of_decide_eq_true h)
  | succ a ih =>
    rcases Bool.or_eq_true_iff.mp h with cap|go
    · exact .capEnd p (of_decide_eq_true cap)
    obtain ⟨m,mem,fit⟩ := List.any_eq_true.mp go
    obtain ⟨f,z⟩ := Bool.and_eq_true_iff.mp fit
    exact .via p m mem (of_decide_eq_true f) (ih z)

private theorem iter_complete {k q p} (path : Reaches k q p) :
    ∀ a, p.1≤a → iter k q a p := by
  induction path with
  | capEnd p hp =>
    intro a _
    cases a <;> simp [iter,hp]
  | via p m mem fit _ ih =>
    intro a ha
    have step : 1≤ m.s ∧ m.s≤ p.1 := by
      obtain ⟨_,_,room⟩ := fit
      simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h|h|h|h|h <;> subst m <;>
        simp [long,medium,short,tiny,root] at room ⊢ <;> omega
    obtain _|a := a
    · omega
    · have tail := ih a (by dsimp [next]; omega)
      change (decide (cap k p) || _)=true
      apply Bool.or_eq_true_iff.mpr; right
      exact List.any_eq_true.mpr ⟨m,mem,Bool.and_eq_true_iff.mpr ⟨decide_eq_true fit,tail⟩⟩

/-- Exact list of exceptions to the current arithmetic schedule below
`u=12`, not exclusions of any physical fans. All long indices at `u=4,5`
are exceptions. -/
def earlyExceptions (u : Nat) : List Nat := match u with
  | 6 => [57,59,61,65,67,71,73,77,79,81,83,85,87,89,91,93]
  | 7 => [59,61,65,67,71,73,79,83,85,89,91,95,97,99,101,103,105,107]
  | 8 => [109,113,115,117,119,121]
  | 9 => [127,131,133,135]
  | 10 => [145,149]
  | 11 => [163]
  | _ => []

private theorem early_exact_check : ∀ (u : Fin 12) (q : Fin 165),
    57≤q.val → q.val+2≤11+14*u.val → q.val%2=1 →
    (iter (11+14*u.val) q.val 165 (start (11+14*u.val) q.val)=true ↔
     6≤u.val ∧ q.val∉earlyExceptions u.val) := by native_decide

theorem early_schedule_iff (u q : Nat) (small : u<12) (lo : 57≤q)
    (hi : q+2≤11+14*u) (odd : q%2=1) :
    Reaches (11+14*u) q (start (11+14*u) q) ↔ 6≤u ∧ q∉earlyExceptions u := by
  have h := early_exact_check ⟨u,small⟩ ⟨q,by omega⟩ lo hi odd
  refine ⟨fun path => h.mp (iter_complete path _ ?_),fun good => iter_sound (h.mpr good)⟩
  dsimp [start]
  omega

-- The uniform schedule starts two progression terms before k=207.
private def feasible (u q : Nat) := iter (11+14*u) q 32 (start (11+14*u) q)
private theorem earlySchedule : ∀ u : Fin 14, ∀ q : Fin 194,
    12≤u.val → 57≤q.val → q.val+2≤11+14*u.val → q.val%2=1 → feasible u q := by native_decide

theorem long_schedule (u q : Nat) (big : 12≤u) (lo : 57≤q) (hi : q+2≤11+14*u) (odd : q%2=1) :
    Reaches (11+14*u) q (start (11+14*u) q) := by
  by_cases e : u<14
  · exact iter_sound (earlySchedule ⟨u,e⟩ ⟨q,by omega⟩ big lo hi odd)
  · have k : 11+14*u=207+14*(u-14) := by omega
    rw [k]; exact cover _ _ lo (by omega) odd

theorem schedule_iff (u q : Nat) (lo : 57≤q) (hi : q+2≤11+14*u) (odd : q%2=1) :
    Reaches (11+14*u) q (start (11+14*u) q) ↔
      12≤u ∨ (6≤u ∧ q∉earlyExceptions u) := by
  by_cases big : 12≤u
  · exact ⟨fun _ => .inl big,fun _ => long_schedule u q big lo hi odd⟩
  · simpa only [big,false_or] using early_schedule_iff u q (by omega) lo hi odd
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed
