import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayLines

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

abbrev Arc (L S : Type) := (L × S) × (L × S)

def forwardArcs {L S : Type} [DecidableEq L]
    (table : List (L × L)) (step : L → L → S → Option S)
    (current : List (L × S)) : List (Arc L S) :=
  current.flatMap fun (a,x) => table.filterMap fun (b,c) =>
    if a=b then (step a c x).map (fun y => ((a,x),(c,y))) else none

theorem forwardArcs_mem {L S : Type} [DecidableEq L]
    {table : List (L × L)} {step : L → L → S → Option S}
    {current : List (L × S)} {a b : L} {x y : S}
    (mem : (a,x)∈current) (edge : (a,b)∈table) (run : step a b x=some y) :
    ((a,x),(b,y))∈forwardArcs table step current := by
  apply List.mem_flatMap.mpr
  refine ⟨(a,x),mem,List.mem_filterMap.mpr ⟨(a,b),edge,?_⟩⟩
  simp [run]

def layers {L S : Type} [DecidableEq L] [DecidableEq S] (tables : Nat → List (L × L))
    (step : Nat → L → L → S → Option S) (base : List (L × S)) :
    Nat → List (L × S)
  | 0 => base
  | j+1 => (forwardStep (tables j) (step j) (layers tables step base j)).dedup

theorem layers_cover {L S : Type} [DecidableEq L] [DecidableEq S]
    {tables : Nat → List (L × L)} {step : Nat → L → L → S → Option S}
    {base : List (L × S)} (line : Nat → L) (state : Nat → S) (last : Nat)
    (init : (line 0,state 0)∈base)
    (edges : ∀ j<last, (line j,line (j+1))∈tables j)
    (runs : ∀ j<last, step j (line j) (line (j+1)) (state j)=some (state (j+1))) :
    ∀ j≤last, (line j,state j)∈layers tables step base j := by
  intro j
  induction j with
  | zero => intro _; exact init
  | succ j ih =>
    intro hj
    rw [layers,List.mem_dedup]
    exact forwardStep_mem (ih (by omega)) (edges j (by omega)) (runs j (by omega))

def backwardArcs {L S : Type} [DecidableEq L] [DecidableEq S]
    (tables : Nat → List (L × L)) (step : Nat → L → L → S → Option S)
    (current : Nat → List (L × S)) (live : List (L × S)) (j : Nat) : List (Arc L S) :=
  (forwardArcs (tables j) (step j) (current j)).filter (fun a => decide (a.2∈live))

def backward {L S : Type} [DecidableEq L] [DecidableEq S]
    (tables : Nat → List (L × L)) (step : Nat → L → L → S → Option S)
    (current : Nat → List (L × S)) (accept : S → Bool) (last : Nat) :
    Nat → List (L × S)
  | 0 => (current last).filter (fun a => accept a.2)
  | k+1 =>
    ((backwardArcs tables step current (backward tables step current accept last k) (last-(k+1))).map Prod.fst).dedup

theorem backward_cover {L S : Type} [DecidableEq L] [DecidableEq S]
    {tables : Nat → List (L × L)} {step : Nat → L → L → S → Option S}
    {current : Nat → List (L × S)} {accept : S → Bool} (last : Nat)
    (line : Nat → L) (state : Nat → S)
    (front : ∀ j≤last, (line j,state j)∈current j)
    (edges : ∀ j<last, (line j,line (j+1))∈tables j)
    (runs : ∀ j<last, step j (line j) (line (j+1)) (state j)=some (state (j+1)))
    (ok : accept (state last)=true) :
    ∀ k≤last, (line (last-k),state (last-k))∈backward tables step current accept last k := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa only [Nat.sub_zero,backward,List.mem_filter] using
      And.intro (front last le_rfl) ok
  | succ k ih =>
    intro hk
    let j := last-(k+1)
    have jl : j<last := by dsimp [j]; omega
    have next : j+1=last-k := by dsimp [j]; omega
    rw [backward,List.mem_dedup]
    apply List.mem_map.mpr
    refine ⟨((line j,state j),(line (j+1),state (j+1))),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact forwardArcs_mem (front j (by omega)) (edges j jl) (runs j jl)
    · apply decide_eq_true
      rw [next]
      exact ih (by omega)

theorem live_pair_cover {L S : Type} [DecidableEq L] [DecidableEq S]
    {tables : Nat → List (L × L)} {step : Nat → L → L → S → Option S}
    {current : Nat → List (L × S)} {accept : S → Bool} (last : Nat)
    (line : Nat → L) (state : Nat → S)
    (front : ∀ j≤last, (line j,state j)∈current j)
    (edges : ∀ j<last, (line j,line (j+1))∈tables j)
    (runs : ∀ j<last, step j (line j) (line (j+1)) (state j)=some (state (j+1)))
    (ok : accept (state last)=true) (j : Nat) (hj : j<last) :
    ((line j,state j),(line (j+1),state (j+1)))∈backwardArcs tables step current
      (backward tables step current accept last (last-(j+1))) j := by
  apply List.mem_filter.mpr
  refine ⟨forwardArcs_mem (front j (by omega)) (edges j hj) (runs j hj),?_⟩
  apply decide_eq_true
  have back := backward_cover last line state front edges runs ok (last-(j+1)) (by omega)
  rwa [show last-(last-(j+1))=j+1 by omega] at back

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
