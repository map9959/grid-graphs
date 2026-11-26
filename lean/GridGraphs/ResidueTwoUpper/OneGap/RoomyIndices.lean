import GridGraphs.ResidueTwoUpper.OneGap.SpeedCover

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed

/-- Pure scheduling arithmetic for the bounded prefix below the
uniform theorem. The search never enumerates masks or physical rows. -/
private def search (k q : Nat) : Nat → State → Bool
  | 0,p => decide (cap k p)
  | n+1,p => decide (cap k p) || (extended :: moves).any fun m =>
      decide (fits k q m p ∧ widthRoom k m p) && search k q n (next m q p)
private theorem soundSearch {k q n p} (ok : search k q n p) : ExtendedRoute k q p := by
  induction n generalizing p with
  | zero => exact .capEnd _ (of_decide_eq_true ok)
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with end'|step
    · exact .capEnd _ (of_decide_eq_true end')
    · obtain ⟨m,mem,hit⟩ := List.any_eq_true.mp step
      obtain ⟨cond,more⟩ := Bool.and_eq_true_iff.mp hit
      exact .via p m mem (of_decide_eq_true cond).1 (of_decide_eq_true cond).2 (ih more)

def remainingTest (u q : Nat) : Bool :=
  let k := 11+14*u; let Y := (q-15)/6
  decide (57≤q ∧ q+2≤k ∧ q%2=1 ∧ k+15*Y+12<4*(q+1)) &&
    !search k q k (start k q)
def longPending := ((List.range 16).flatMap fun u =>
    ((List.range (11+14*u)).filter (remainingTest u)).map (u,·))

theorem pending_or_route {u q : Nat} (lo : 57≤q) (hi : q+2≤11+14*u) (odd : q%2=1)
    (narrow : 11+14*u+15*((q-15)/6)+12<4*(q+1)) :
    (u,q)∈longPending ∨ ExtendedRoute (11+14*u) q (start (11+14*u) q) := by
  by_cases big : 16≤u
  · exact .inr (roomy_uniform (by omega) lo hi odd).extend
  by_cases path : search (11+14*u) q (11+14*u) (start (11+14*u) q)
  · exact .inr (soundSearch path)
  left; apply List.mem_flatMap.mpr
  refine ⟨u,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨q,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,rfl⟩⟩
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨lo,hi,odd,narrow⟩,by simpa using path⟩

/-- Four long advances leave 39 rows and column 152. The medium read
then reaches the cap: its upper tooth budget is exactly 179. -/
theorem route_179_175 : Roomy 179 175 (start 179 175) := by
  iterate 4 apply RoomyWith.via _ long (by decide) (by decide) (by decide)
  exact .via _ medium (by decide) (by decide) (by decide) (.capEnd _ (by decide))

theorem route_165 {q : Nat} (h : q=161 ∨ q=163) : ExtendedRoute 165 q (start 165 q) := by
  rcases h with rfl|rfl <;>
    (iterate 2 apply RoomyWith.via _ extended (by decide) (by decide) (by decide)) <;>
    exact .via _ medium (by decide) (by decide) (by decide) (.capEnd _ (by decide))

theorem longPending_checked : longPending.length=60 ∧ longPending.Nodup ∧
    longPending.all (fun p => decide (p.1≤10)) := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed
