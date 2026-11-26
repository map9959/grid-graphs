import GridGraphs.ResidueTwoUpper.OneGap.SouthCapInterface

/-! Sound backward projection for a fixed rectangular strip, without
either axis filter. This layer is independent of the representation of
forest states. A trace has to pass the actual row-transition relation;
no enumeration of physical boards is part of the soundness proof. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open L7 FanSlab

inductive Axis where
  | horizontal | vertical
deriving DecidableEq

/-- `j` runs along the sweep and `i` across the strip. Coordinates
always return to the untransposed catalogue order. -/
def cell (axis : Axis) (start j i : Nat) : Nat × Nat :=
  match axis with
  | .horizontal => (start+i,j)
  | .vertical => (j,start+i)

abbrev Tiles := Nat → Nat → Nat
abbrev Domains := Nat → Nat → Word → Prop

def word (t : Tiles) (r c : Nat) : Word :=
  (t r c,t r (c+1),t (r+1) c,t (r+1) (c+1))

def band (t : Tiles) (axis : Axis) (start : Nat) : Tiles :=
  fun j i => t (cell axis start j i).1 (cell axis start j i).2

/-- Word reconstructed from two consecutive sweep lines. The bank
order is NW, NE, SW, SE, even when the sweep is vertical. -/
def acrossWord (axis : Axis) (b : Tiles) (j i : Nat) : Word :=
  match axis with
  | .horizontal => (b j i,b (j+1) i,b j (i+1),b (j+1) (i+1))
  | .vertical => (b j i,b j (i+1),b (j+1) i,b (j+1) (i+1))

theorem acrossWord_band (t : Tiles) (axis : Axis) (start j i : Nat) :
    acrossWord axis (band t axis start) j i =
      word t (cell axis start j i).1 (cell axis start j i).2 := by
  cases axis <;> simp only [acrossWord,band,word,cell,Nat.add_assoc]

structure Window (H W : Nat) where
  axis : Axis
  start : Nat
  depth : Nat
  depth_min : 2≤depth
  fits : start+depth≤(match axis with
    | .horizontal => H
    | .vertical => W)

namespace Window
variable {H W : Nat} (s : Window H W)

def length : Nat := match s.axis with
  | .horizontal => W
  | .vertical => H

def Inside (r c : Nat) : Prop :=
  ∃ j i, j+2 ≤ s.length ∧ i+2 ≤ s.depth ∧ cell s.axis s.start j i=(r,c)

theorem cell_fits {j i : Nat} (hj : j+2 ≤ s.length) (hi : i+2 ≤ s.depth) :
    (cell s.axis s.start j i).1+2≤H ∧ (cell s.axis s.start j i).2+2≤W := by
  cases s with
  | mk axis start depth depth_min fits =>
    cases axis
    · change start+depth≤H at fits
      dsimp [length,cell] at hj hi ⊢
      omega
    · change start+depth≤W at fits
      dsimp [length,cell] at hj hi ⊢
      omega

/-- Parameterize over the actual sequential forest transition.
`step j` consumes tile-line `j`, not the overlapping plaquette at `j`.
The initial and final checks can differ, e.g. final disappearance of
a marked component not touching any open site. -/
structure Sweep (State : Type) where
  base : State
  step : Nat → State → (Nat → Nat) → State → Prop
  final : State → Prop

def HasTrace {State : Type} (a : Sweep State) (b : Tiles) : Prop :=
  ∃ z : Nat → State, z 0=a.base ∧
    (∀ j<s.length, a.step j (z j) (b j) (z (j+1))) ∧ a.final (z s.length)

def Consistent (D : Domains) (b : Tiles) : Prop :=
  ∀ j i, j+2 ≤ s.length → i+2 ≤ s.depth →
    D (cell s.axis s.start j i).1 (cell s.axis s.start j i).2 (acrossWord s.axis b j i)

/-- A projected word has a whole accepted strip as a witness (the
semantic forward/backward support). Outside the strip nothing changes. -/
noncomputable def prune {State : Type} (a : Sweep State) (D : Domains) : Domains := by
  classical
  exact fun r c m => if s.Inside r c then
    ∃ b : Tiles, s.Consistent D b ∧ s.HasTrace a b ∧
      ∃ j i, j+2 ≤ s.length ∧ i+2 ≤ s.depth ∧ cell s.axis s.start j i=(r,c) ∧
        acrossWord s.axis b j i=m
    else D r c m

end Window

def Admitted (H W : Nat) (D : Domains) (t : Tiles) : Prop :=
  ∀ r c, r+2≤H → c+2≤W → D r c (word t r c)

theorem admitted_consistent {H W} (s : Window H W) {D : Domains} {t : Tiles}
    (h : Admitted H W D t) : s.Consistent D (band t s.axis s.start) := by
  intro j i hj hi
  rw [acrossWord_band]
  exact h _ _ (s.cell_fits hj hi).1 (s.cell_fits hj hi).2

/-- A single axis-free backward projection preserves every word of a
physical tile field, provided that its own strip has a forest trace.
All witnesses come from that same field; local supporters need not be
chosen independently and no choice of an axis can change the marks. -/
theorem survives_update {H W State} (s : Window H W) (a : Window.Sweep State)
    {D : Domains} {t : Tiles}
    (h : Admitted H W D t) (trace : s.HasTrace a (band t s.axis s.start)) :
    Admitted H W (s.prune a D) t := by
  classical
  intro r c hr hc
  unfold Window.prune
  split
  · rename_i inside
    obtain ⟨j,i,hj,hi,rc⟩ := inside
    refine ⟨band t s.axis s.start,admitted_consistent s h,trace,j,i,hj,hi,rc,?_⟩
    rw [acrossWord_band,rc]
  · exact h r c hr hc

noncomputable def sweepAll {H W State} (updates : List (Window H W × Window.Sweep State))
    (D : Domains) : Domains :=
  updates.foldl (fun D (s,a) => s.prune a D) D

theorem survives_updates {H W State} (updates : List (Window H W × Window.Sweep State))
    {D : Domains} {t : Tiles} (h : Admitted H W D t)
    (traces : ∀ p ∈ updates, p.1.HasTrace p.2 (band t p.1.axis p.1.start)) :
    Admitted H W (sweepAll updates D) t := by
  induction updates generalizing D with
  | nil => exact h
  | cons p ps ih =>
    exact ih (survives_update p.1 p.2 h (traces p (by simp)))
      (fun p hp => traces p (List.mem_cons_of_mem _ hp))

def cropTiles {n : Nat} (F : Finset (GridVertex n n)) (v : View) (k h : Nat) : Tiles :=
  fun r c => square F v (firstRow k h+3*r) (firstCol k h+3*c)

/-- The axis-free bank, with just the physical top suffix imposed.
The producer's transposed mask 7 is row-major mask 73 here. -/
def initialDomains (h : Nat) : Domains :=
  fun r c m => widened ordinary (endTag h r) (endTag (width h) c) m ∧
    (r=0 → m.1=73 ∧ m.2.1=73)

theorem physical_initially_admitted {n : Nat} (F : Finset (GridVertex n n)) (v : View)
    (k h : Nat) (fits : width h ≤ k)
    (top : ∀ i, k-width h ≤ i → i < k → square F v (firstRow k h) (1+3*i)=73)
    (bank : OrdinaryCapAdmitted F v k h) :
    Admitted h (width h) (initialDomains h) (cropTiles F v k h) := by
  intro r c hr hc
  constructor
  · have adm := bank r c hr hc
    simpa [word,cropTiles,Nat.mul_add,Nat.add_assoc] using adm
  · rintro rfl
    have atCol (j : Nat) (hj : j<width h) :
        cropTiles F v k h 0 j=73 := by
      have i := top (k-width h+j) (by omega) (by omega)
      simpa [cropTiles,firstCol,Nat.mul_add,Nat.add_assoc] using i
    exact ⟨atCol c (by omega),atCol (c+1) (by omega)⟩

/-- Once the physical traces are constructed, the very same crop
survives every update, regardless of the order of the two axes. -/
theorem physical_survives_updates {n : Nat} {State : Type}
    (F : Finset (GridVertex n n)) (v : View) (k h : Nat) (fits : width h ≤ k)
    (top : ∀ i, k-width h ≤ i → i < k → square F v (firstRow k h) (1+3*i)=73)
    (bank : OrdinaryCapAdmitted F v k h)
    (updates : List (Window h (width h) × Window.Sweep State))
    (traces : ∀ p ∈ updates,
      p.1.HasTrace p.2 (band (cropTiles F v k h) p.1.axis p.1.start)) :
    Admitted h (width h) (sweepAll updates (initialDomains h)) (cropTiles F v k h) :=
  survives_updates updates (physical_initially_admitted F v k h fits top bank) traces

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
