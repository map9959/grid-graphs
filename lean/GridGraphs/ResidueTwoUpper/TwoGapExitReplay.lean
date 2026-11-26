import GridGraphs.ResidueTwoUpper.TwoGapFoldedPlaquette

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay

abbrev Word := Nat × Nat × Nat
abbrev Band := Nat × Nat × Nat × Nat
def tables : List (List Band) :=
  ((include_str "Data/two_gap_exit_strip.txt").trimAscii.toString.splitOn "\n").map fun line =>
    (line.splitOn " ").map fun s =>
      let z := s.toNat!
      (z%512,z/512%512,z/512^2%512,z/512^3%512)

structure Frontier where
  last : Nat
  parts : Array Nat
  tags : Array Nat
  deriving DecidableEq, Inhabited

abbrev State := Word × Frontier
def base : Frontier := ⟨512,(List.range 10).toArray,#[0,0,0,0,0,0,0,0,0,1]⟩

/-- Parts store direct component labels. Indices 0..8 are the old row,
9 is the common root, and 10..18 the new row. Tag bit 0 means access
to a side or root; bit 1 means that the component contains a mark. -/
def link (parts tags : Array Nat) (x y : Nat) : Option (Array Nat × Array Nat) := do
  let a := parts[x]!
  let b := parts[y]!
  if a=b then none else
    return (parts.map (fun c => if c=a then b else c),tags.set! b (tags[a]! ||| tags[b]!))

def advance (s : Frontier) (m teeth : Nat) : Option Frontier := do
  let mut p := s.parts ++ ((List.range 9).map (·+10)).toArray
  let mut t := s.tags ++ ((List.range 9).map fun i =>
    (if m.testBit i then 2 else 0) + (if i=0 ∨ i=8 then 1 else 0)).toArray
  for i in [:9] do
    if s.last<512 && (s.last ||| m).testBit i then
      (p,t) ← link p t i (10+i)
    if i>0 && (m.testBit (i-1) || m.testBit i) then
      (p,t) ← link p t (9+i) (10+i)
    if (m &&& teeth).testBit i then
      (p,t) ← link p t (10+i) 9
  let live := ((List.range 9).map fun i => p[10+i]!) ++ [p[9]!]
  for i in [:9] do
    if t[p[i]!]! = 2 && !live.contains p[i]! then return ← none
  return ⟨m,(live.map live.idxOf).toArray,(live.map (fun c => t[c]!)).toArray⟩

def line (w : Word) (r : Nat) := ((List.range 9).map fun i =>
  let mask := if i<3 then w.1 else if i<6 then w.2.1 else w.2.2
  ((mask >>> (3*(i%3)+r))%2) <<< i).sum

def push (s : Frontier) (w : Word) (teeth : Nat) : Option Frontier := do
  let a ← advance s (line w 0) 0
  let b ← advance a (line w 1) teeth
  advance b (line w 2) 0

def step (tab : List Band) (teeth : Nat) (states : List State) : List State :=
  (states.flatMap fun ⟨⟨x,z,k⟩,s⟩ => tab.flatMap fun ⟨a,b,c,d⟩ =>
    if a=x && c=z then tab.filterMap fun ⟨e,f,g,h⟩ =>
      if e=z && f=d && g=k then (push s (b,d,h) teeth).map ((b,d,h),·) else none
    else []).eraseDups

def init : List State := ((push base (48,48,48) 495).map ((48,48,48),·)).toList
def seed := step tables[1]! 0 (step tables[0]! 0 init)
def middle := step tables[2]! 0 seed
def accepted (count : Nat) :=
  step tables[4]! 511 (step tables[3]! 0 ((step tables[2]! 0)^[count] seed))

private theorem stable : step tables[2]! 0 middle = middle := by native_decide
private theorem finish : step tables[4]! 511 (step tables[3]! 0 middle)=[] := by native_decide

/-- Both overlapping tuples must use the actual two middle masks. -/
def permits (tab : List Band) (top bot : Word) : Prop :=
  (top.1,bot.1,top.2.1,bot.2.1) ∈ tab ∧ (top.2.1,bot.2.1,top.2.2,bot.2.2) ∈ tab

theorem step_mem {ss : List State} {top bot : Word} {s t : Frontier} {tab teeth}
    (hs : (top,s) ∈ ss) (ok : permits tab top bot) (p : push s bot teeth=some t) :
    (bot,t) ∈ step tab teeth ss := by
  rcases top with ⟨a,c,e⟩
  rcases bot with ⟨b,d,f⟩
  unfold step
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨_,hs,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨_,ok.1,?_⟩
  simp only [beq_self_eq_true,Bool.and_self,decide_true,if_true,List.mem_filterMap]
  exact ⟨_,ok.2,by simp [p]⟩

theorem middle_count : middle.length=13 := by native_decide
theorem replay_empty (t : Nat) : accepted (t+1)=[] := by
  have h : ∀ r : Nat, (step tables[2]! 0)^[r+1] seed=middle := by
    intro r; induction r with
    | zero => rfl
    | succ r ih => rw [Function.iterate_succ_apply',ih,stable]
  unfold accepted; rw [h,finish]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
