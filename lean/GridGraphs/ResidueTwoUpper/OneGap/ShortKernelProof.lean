import GridGraphs.ResidueTwoUpper.OneGap.ShortKernel
import GridGraphs.ResidueTwoUpper.OneGap.Short77Replay
import GridGraphs.ResidueTwoUpper.OneGap.ShortCache

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7

private theorem prune_eq (s k : Nat) (A : Board) : Kernel.prune s k A=prune s k A := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih _
private theorem tight_eq (h w : Nat) (v : Bool) (k : Nat) (a : Sheet) :
    Kernel.tighten h w v k a=tighten h w v k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    unfold Kernel.tighten tighten; dsimp only
    change (if _ then _ else Kernel.tighten h w v k _)=(if _ then _ else tighten h w v k _)
    rw [ih]; rfl
private theorem sweep_eq (s : Nat) (v : Bool) (k : Nat) (a : Board) : Kernel.sweep s v k a=pairSweep s v k a := by
  unfold Kernel.sweep pairSweep; rw [tight_eq]; rfl
private theorem run_eq (s k : Nat) (a : Board) : Kernel.run s k a=fromPairs s k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => unfold Kernel.run fromPairs; simp only [sweep_eq,ih]; rfl
theorem kernel_kept {s M A} (e : Agree s M) (h : Kept s M A) (k : Nat) :
    Kept s M (Kernel.prune s k A) := by rw [prune_eq]; exact prune_kept h e k

@[noinline] def pairTest (s n q : Nat) (w : View) (a : Board) :=
  Kernel.run s 8 (Kernel.prune s 18 (planted n q w a))
theorem kernel_excludes {s k t M A} (ok : Kernel.run s k (Kernel.prune s t A))
    (h : Agree s M) (kept : Kept s M A) : False := by
  rw [prune_eq,run_eq] at ok
  exact fromPairs_sound ok h (prune_kept kept h t)
theorem test_excludes (u q : Nat) (w : View) (ok : pairTest (33+42*u) (35+42*u) q w (cached u chart))
    {F : Finset (GridVertex (35+42*u) (35+42*u))} {P} (S : Seed F P w q) (acy : (ResidueZero.Bonds F).IsAcyclic) : False := by
  unfold pairTest at ok; rw [cached_eq,prune_eq,run_eq] at ok
  have h := actual_agree F P S.step S.owners
  have kept := kept_physical S acy
  rw [show 35+42*u-2=33+42*u by omega] at h kept
  exact fromPairs_sound ok h (prune_kept kept h 18)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
