import GridGraphs.ResidueTwoUpper.OneGap.L7Data
import Mathlib

/-! The two seven-row scans use exactly the same four junction bits.
No lower bound is imposed on the number of visible charged patches.
`mid_check` is closure of the entire set of labeled mask-pairs, not an
equality of counts. It permits any number of three-column insertions. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7

def lane (m i : Nat) := (m >>> i)%2
def spread (m : Nat) := lane m 0 + 8*lane m 1 + 64*lane m 2
def window (a b c r : Nat) := spread (a>>>r)+2*spread (b>>>r)+4*spread (c>>>r)
-- The far fringe cell can be omitted, including for the junction test.
def band (j a b c : Nat) := (List.range 5).all fun r =>
  (r==4 && j==31) || allowed r j (window a b c r)
def preset (n : Nat) (sw far : Bool) (r j : Nat) : Option Bool :=
  if r=0 then
    some (if j=1 ∨ j=2 then sw else if j+2=n then far else true)
  else if j=0 then some (if r=1 ∨ r=2 then !sw else true)
  else if j+1=n then some (if r=1 then !far else true)
  else if r=1 ∨ j=1 ∨ j+2=n then some false else none
def columnOK (n : Nat) (sw far : Bool) (j m : Nat) :=
  (List.range 7).all fun r => match preset n sw far r j with
    | none => true | some b => lane m r == b.toNat
def opt (sw far : Bool) (j : Nat) := (List.range 128).filter (columnOK 35 sw far j)

-- Physical junction bits at (2,5),(3,5),(4,5),(5,6), after putting
-- the open arm horizontally. On the other arm read the transposed sites.
def observe (sw : Bool) (j m : Nat) :=
  if sw then
    (if j=2 then lane m 5 else 0)+(if j=3 then 2*lane m 5 else 0)+
    (if j=4 then 4*lane m 5 else 0)+(if j=5 then 8*lane m 6 else 0)
  else (if j=5 then lane m 2+2*lane m 3+4*lane m 4 else 0)+
    (if j=6 then 8*lane m 5 else 0)
abbrev State := Nat × Nat × Nat
def initial (s f : Bool) : List State := (opt s f 0).flatMap fun a =>
  (opt s f 1).map fun b => (a,b,observe s 0 a+observe s 1 b)
def succs (s f : Bool) (j : Nat) (v : State) : List State :=
  ((opt s f (j+2)).filter (band j v.1 v.2.1)).map fun c => (v.2.1,c,v.2.2+observe s (j+2) c)
def states (s f : Bool) : Nat → List State
  | 0 => initial s f
  | j+1 => ((states s f j).flatMap (succs s f j)).eraseDups

def midOK (s f : Bool) :=
  let earlier := states s f 21
  (states s f 24).all earlier.contains
def outputOK (s f : Bool) := (states s f 33).all fun v =>
  (if s then [0,1,3,11] else [2,5,8,9,10]).contains v.2.2

def fold (u j : Nat) :=
  if j<21 then j else if j<21+42*u then 21+(j-21)%3 else j-42*u

theorem fold_step (u j : Nat) :
    fold u (j+1)=fold u j+1 ∨ (fold u j=23 ∧ fold u (j+1)=21) := by
  unfold fold; split_ifs <;> omega

def label (s : Bool) (X : Nat → Nat) (i : Nat) := ∑ j ∈ Finset.range i, observe s j (X j)

theorem scan_sound (u : Nat) (s f : Bool) (X : Nat → Nat) (lt : ∀ j, X j<128)
    (fr : ∀ j<35+42*u, columnOK (35+42*u) s f j (X j))
    (localOK : ∀ j<33+42*u, band (fold u j) (X j) (X (j+1)) (X (j+2)))
    (middle : midOK s f) (out : outputOK s f) :
    label s X (35+42*u) ∈ (if s then [0,1,3,11] else [2,5,8,9,10]) := by
  have col (j t : Nat) (hj : j<33+42*u) (ht : t≤2) :
      X (j+t)∈opt s f (fold u j+t) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (lt _),?_⟩
    have hh := fr (j+t) (by omega)
    have eq (r : Nat) : preset (35+42*u) s f r (j+t)=preset 35 s f r (fold u j+t) := by
      unfold preset fold
      split_ifs <;> first | rfl | omega
    simpa only [columnOK,eq] using hh
  have obs (j : Nat) : observe s (fold u j+2) (X (j+2))=observe s (j+2) (X (j+2)) := by
    by_cases h : j<21
    · simp [fold,h]
    have big : 21≤fold u j := by unfold fold; split_ifs <;> omega
    simp [observe,show fold u j≠0 by omega,show j≠0 by omega,show fold u j+2≠3 by omega,
      show fold u j+2≠4 by omega,show fold u j+2≠5 by omega,show fold u j+2≠6 by omega,
      show j+2≠3 by omega,show j+2≠4 by omega,
      show j+2≠5 by omega,show j+2≠6 by omega]
  have reach (j : Nat) (hj : j≤33+42*u) :
      (X j,X (j+1),label s X (j+2)) ∈ states s f (fold u j) := by
    induction j with
    | zero =>
      simp only [fold,show 0<21 by decide,if_true,states,initial,List.mem_flatMap,List.mem_map]
      have a := col 0 0 (by omega) (by decide)
      have b := col 0 1 (by omega) (by decide)
      exact ⟨X 0,a,X 1,b,by simp [label,Finset.sum_range_succ]⟩
    | succ j ih =>
      have reach := ih (by omega)
      have h : (X (j+1),X (j+2),label s X (j+3))∈ states s f (fold u j+1) := by
        rw [states,List.mem_eraseDups,List.mem_flatMap]
        refine ⟨_,reach,?_⟩
        simp only [succs,List.mem_map,List.mem_filter]
        exact ⟨_,⟨col j 2 (by omega) (by decide),localOK j (by omega)⟩,
          by simp [obs,label,Finset.sum_range_succ]⟩
      rcases fold_step u j with eq|⟨eq,back⟩
      · rwa [eq]
      · rw [eq] at h
        rw [back]
        exact List.contains_iff_mem.mp (List.all_eq_true.mp middle _ h)
  have done := reach (33+42*u) le_rfl
  rw [show fold u (33+42*u)=33 by unfold fold; split_ifs <;> omega] at done
  have bill := List.contains_iff_mem.mp (List.all_eq_true.mp out _ done)
  simpa only [show 33+42*u+2=35+42*u by omega] using bill

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
