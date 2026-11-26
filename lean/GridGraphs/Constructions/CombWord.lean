import Mathlib

/-! Explicit period certificate for the four-row cap transfer. The labels
are component names, not parent pointers; inserting an edge replaces one
name by the other throughout the frontier. No pair already connected may
be joined. This file proves acceptance and score in the transfer model. -/
namespace GridGraphs.CombWord

structure Frontier where
  phase : Nat
  first : Bool
  old : Nat
  parts : List Nat
deriving DecidableEq, Repr

def start : Frontier := ⟨0,true,0,[0,1,2,3,4,5]⟩
def seam : Frontier := ⟨1,false,7,[0,1,0,0,0,0]⟩

def merge (p : List Nat) (ab : Nat × Nat) : Option (List Nat) := do
  let a ← p[ab.1]?
  let b ← p[ab.2]?
  guard (a ≠ b)
  return p.map (fun c => if c = a then b else c)

def columnEdges (s : Frontier) (m : Nat) : List (Nat × Nat) := Id.run do
  let top := if s.phase = 0 || m.testBit 0 then [(0,6)] else []
  let bot := if m.testBit 3 then [(1,9)] else []
  let vert := ((List.range 3).filter fun i => m.testBit i || m.testBit (i+1)).map
    fun i => (6+i,7+i)
  let horiz := if s.first then [] else
    ((List.range 4).filter fun i => m.testBit i || s.old.testBit i).map fun i => (2+i,6+i)
  return top ++ bot ++ vert ++ horiz

def retained : List Nat := [0,1,6,7,8,9]

def step (s : Frontier) (m : Nat) : Option Frontier := do
  guard (m < 16)
  guard ((((s.old <<< 1) ||| (s.old >>> 1)) &&& m) = 0)
  guard (s.first || s.phase != 0 || !(s.old.testBit 0))
  let p ← (columnEdges s m).foldlM merge (s.parts ++ [6,7,8,9])
  let q ← retained.mapM fun i => p[i]?
  return ⟨(s.phase+1)%3,false,m,q.map q.idxOf⟩

def run (s : Frontier) (w : List Nat) := w.foldlM step s
def marks (w : List Nat) := (w.map fun m => ((List.range 4).filter m.testBit).length).sum

def loopWord : List Nat :=
  [0,8,3,0,12,1,0,14,0,2,8,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]

def ending : Nat → List Nat
  | 3 => [0,12,1,4,4,1,8,0,7]
  | 4 => [0,12,1,4,4,4,4,4,1,8,0,7]
  | 5 => [0,8,3,0,12,1,4,4,5,4,4,1,8,0,7]
  | 6 => [0,12,1,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | 7 => [0,12,1,4,4,4,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | 8 => [0,8,3,0,12,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | 9 => [0,12,1,0,14,0,2,8,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | 10 => [0,12,1,4,4,1,8,2,2,2,8,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | 11 => [0,8,3,0,12,1,0,14,0,2,8,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7,0,0,15]
  | 12 => [0,8,3,0,12,1,4,4,5,4,4,1,8,2,2,2,8,1,4,4,5,4,4,1,8,2,0,14,0,1,12,0,3,8,0,7]
  | _ => []

set_option maxRecDepth 8192 in
theorem cycle_check : run seam loopWord = some seam ∧ marks loopWord = 33 ∧
    loopWord.length = 30 := by decide

set_option maxRecDepth 8192 in
private theorem end_check (r : Nat) (lo : 3 ≤ r) (hi : r ≤ 12) :
    (run seam (ending r)).isSome ∧ (ending r).length = 3*r ∧
      marks (ending r) = 3*r+(3*r+7)/10 := by
  interval_cases r <;> decide

def cycles : Nat → List Nat
  | 0 => []
  | t+1 => loopWord ++ cycles t

private theorem append_run {s t : Frontier} {u : List Nat}
    (h : run s u = some t) (v : List Nat) : run s (u++v) = run t v := by
  simp [run, List.foldlM_append, run] at h ⊢
  rw [h]
  rfl

private theorem cycles_check (t : Nat) :
    run seam (cycles t) = some seam ∧ marks (cycles t) = 33*t ∧
      (cycles t).length = 30*t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [cycles, append_run cycle_check.1]
    refine ⟨ih.1, ?_, ?_⟩
    · simp only [marks, List.map_append, List.sum_append]
      change marks loopWord + marks (cycles t) = _
      rw [cycle_check.2.1, ih.2.1]; omega
    · rw [List.length_append, cycle_check.2.2, ih.2.2]; omega

/-- The witnesses are single accepted words, not independent bounds on
fragments. `3r + 3 + (3r+7)/10` uses no truncated negative dividend. -/
theorem exists_cap (k : Nat) (hk : 3 ≤ k) :
    ∃ w, (run start w).isSome ∧ w.length = 3*k+1 ∧
      marks w = 3*k+3+(3*k+7)/10 := by
  let t := (k-3)/10
  let r := (k-3)%10+3
  have split : k = 10*t+r := by dsimp [t,r]; omega
  have h := end_check r (by dsimp [r]; omega) (by dsimp [r]; omega)
  have hc := cycles_check t
  have first : run start [7] = some seam := by decide
  refine ⟨[7] ++ (cycles t ++ ending r), ?_, ?_, ?_⟩
  · rw [append_run first, append_run hc.1]
    exact h.1
  · simp only [List.length_append, List.length_cons, List.length_nil, hc.2.2,h.2.1]
    omega
  · simp only [marks, List.map_append, List.sum_append]
    change 3 + (marks (cycles t) + marks (ending r)) = _
    rw [hc.2.1,h.2.2]; omega

end GridGraphs.CombWord
