import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayPairs

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

/-- Finite forward support on compatible consecutive line pairs.
The code is parameterized by the packed machine's line transition;
the proof does not trust any external rejection or any memoization. -/
def forwardStep {L S : Type} [DecidableEq L]
    (table : List (L × L)) (step : L → L → S → Option S)
    (current : List (L × S)) : List (L × S) :=
  current.flatMap fun (a,s) => table.filterMap fun (b,c) =>
    if a=b then (step a c s).map (c,·) else none

def forward {L S : Type} [DecidableEq L] (tables : Nat → List (L × L))
    (step : Nat → L → L → S → Option S) (base : List (L × S)) :
    Nat → List (L × S)
  | 0 => base
  | j+1 => forwardStep (tables j) (step j) (forward tables step base j)

theorem forwardStep_mem {L S : Type} [DecidableEq L]
    {table : List (L × L)} {step : L → L → S → Option S}
    {current : List (L × S)} {a b : L} {x y : S}
    (mem : (a,x)∈current) (edge : (a,b)∈table) (run : step a b x=some y) :
    (b,y)∈forwardStep table step current := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,x),mem,List.mem_filterMap.mpr ⟨(a,b),edge,?_⟩⟩
  simp [run]

/-- Any genuine trace stays in the forward support sets, even if
the line table or initial set includes extra candidates. -/
theorem forward_covers {L S : Type} [DecidableEq L] (tables : Nat → List (L × L))
    (step : Nat → L → L → S → Option S) (base : List (L × S))
    (line : Nat → L) (state : Nat → S) (length : Nat)
    (init : (line 0,state 0)∈base)
    (edges : ∀ j<length, (line j,line (j+1))∈tables j)
    (runs : ∀ j<length, step j (line j) (line (j+1)) (state j)=some (state (j+1))) :
    ∀ j≤length, (line j,state j)∈forward tables step base j := by
  intro j
  induction j with
  | zero => intro _; exact init
  | succ j ih =>
    intro len
    have hj : j<length := by omega
    exact forwardStep_mem (ih (by omega)) (edges j hj) (runs j hj)

def acceptsForward {L S : Type} (accept : S → Bool) (states : List (L × S)) : Bool :=
  states.any (fun x => accept x.2)

theorem forward_rejection_sound {L S : Type} [DecidableEq L] (tables : Nat → List (L × L))
    (step : Nat → L → L → S → Option S) (base : List (L × S)) (accept : S → Bool) (length : Nat)
    (reject : acceptsForward accept (forward tables step base length)=false) :
    ¬∃ (line : Nat → L) (state : Nat → S),
      (line 0,state 0)∈base ∧
      (∀ j<length, (line j,line (j+1))∈tables j) ∧
      (∀ j<length, step j (line j) (line (j+1)) (state j)=some (state (j+1))) ∧
      accept (state length)=true := by
  rintro ⟨line,state,init,edges,runs,ok⟩
  have final := forward_covers tables step base line state length init edges runs length le_rfl
  have no := List.any_eq_false.mp reject (line length,state length) final
  exact no ok

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
