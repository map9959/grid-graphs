import GridGraphs.ResidueTwoUpper.OneGap.ShortPair

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7
def fromPairs (s : Nat) (budget : Nat) (A : Board) : Bool :=
  match budget with
  | 0 => emptyAt A s
  | t+1 =>
    let H := pairSweep s false 35 A
    emptyAt H s || fromPairs s t (pairSweep s true 35 H)

theorem fromPairs_sound {s M A t} (ok : fromPairs s t A) (e : Agree s M) (h : Kept s M A) : False := by
  induction t generalizing A with
  | zero => exact reject_sound (fuel:=0) (by simpa only [reject,fromPairs] using ok) e h
  | succ t ih =>
    have h' := pairSweep_sound e h false 35
    rcases Bool.or_eq_true_iff.mp ok with empty|next
    · exact reject_sound (fuel:=0) (by simpa only [reject] using empty) e h'
    · exact ih next (pairSweep_sound e h' true 35)

@[noinline] def small77 (q : Nat) (w : View) (A : Board) :=
  fromPairs 75 8 (prune 75 18 (planted 77 q w A))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
