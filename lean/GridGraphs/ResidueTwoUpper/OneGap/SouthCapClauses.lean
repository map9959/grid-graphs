import GridGraphs.ResidueTwoUpper.OneGap.SouthCapWindow
import Std.Sat.CNF.Dimacs

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open Std.Sat

inductive Wire (V : Type) where
  | mark : V → Wire V
  | arc : V → V → Wire V
  | sheet : V → Wire V
deriving DecidableEq

abbrev Rows (V : Type) := List (CNF.Clause (Wire V))

def value {V : Type} (W : WindowField V) : Wire V → Bool
  | .mark x => W.mark x
  | .arc x y => W.arrow x y
  | .sheet x => W.sheet x

def Holds {V : Type} (W : WindowField V) (rows : Rows V) : Prop :=
  ∀ c ∈ rows, c.eval (value W)=true

/-- The five clauses emitted for an edge by `defect_window.window`. -/
def edgeRows {V : Type} (x y : V) : Rows V :=
  [[(.mark x,false),(.arc x y,true),(.arc y x,true)],
   [(.mark y,false),(.arc x y,true),(.arc y x,true)],
   [(.arc x y,false),(.arc y x,false)],
   [(.arc x y,false),(.mark x,true),(.mark y,true)],
   [(.arc y x,false),(.mark x,true),(.mark y,true)]]

/-- The two clauses for a turn, with the sheet sign reversed across
the cut in the compass. -/
def turnRows {V : Type} (x y z : V) (wrap : Bool) : Rows V :=
  [[(.arc x y,false),(.arc y z,false),(.sheet x,false),(.sheet y,!wrap)],
   [(.arc x y,false),(.arc y z,false),(.sheet x,true),(.sheet y,wrap)]]

def choiceRow {V : Type} (x y z : V) : Rows V :=
  [[(.arc x y,false),(.arc x z,false)]]

def rootRow {V : Type} (x y : V) : Rows V := [[(.arc x y,false)]]

theorem edgeRows_iff {V : Type} (W : WindowField V) (x y : V) :
    Holds W (edgeRows x y) ↔
      (W.arrow x y || W.arrow y x)=(W.mark x || W.mark y) ∧
      (W.arrow x y && W.arrow y x)=false := by
  simp only [Holds,edgeRows,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,
    CNF.Clause.eval,List.any_cons,List.any_nil,value]
  cases hx : W.mark x <;> cases hy : W.mark y <;>
    cases a : W.arrow x y <;> cases b : W.arrow y x <;>
    simp

theorem turnRows_iff {V : Type} (W : WindowField V) (x y z : V) (wrap : Bool) :
    Holds W (turnRows x y z wrap) ↔
      (W.arrow x y=true → W.arrow y z=true → W.sheet y=xor (W.sheet x) wrap) := by
  simp only [Holds,turnRows,List.forall_mem_cons,List.not_mem_nil,
    CNF.Clause.eval,List.any_cons,List.any_nil,value]
  cases a : W.arrow x y <;> cases b : W.arrow y z <;>
    cases sx : W.sheet x <;> cases sy : W.sheet y <;> cases wrap <;>
    simp

theorem physical_edge_rows {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y : Slots h w r c)
    (adj : adjacent 18 18 x.1 y.1) :
    Holds (windowField pl H) (edgeRows x y) := by
  apply (edgeRows_iff ..).mpr
  obtain ⟨a,b⟩ := window_edges pl H x y
  refine ⟨a.trans ?_,b⟩
  simp [adj]

theorem physical_turn_rows {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y z : Slots h w r c) :
    Holds (windowField pl H) (turnRows x y z (decide
      ((dir (pl.point v x) (pl.point v y)=0 ∧ dir (pl.point v y) (pl.point v z)=3) ∨
       (dir (pl.point v x) (pl.point v y)=3 ∧ dir (pl.point v y) (pl.point v z)=0)))) :=
  (turnRows_iff ..).mpr (window_turn pl H x y z)

theorem physical_choice_row {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y z : Slots h w r c) (ne : y≠z) :
    Holds (windowField pl H) (choiceRow x y z) := by
  simp only [Holds,choiceRow,List.forall_mem_cons,List.not_mem_nil,
    CNF.Clause.eval,List.any_cons,List.any_nil,value]
  have unique : H.parent (pl.point v x)=pl.point v y →
      H.parent (pl.point v x)≠pl.point v z := by
    intro a b
    exact ne (pl.point_injective v (a.symm.trans b))
  simp [windowField]
  tauto

theorem physical_root_row {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y : Slots h w r c)
    (root : atlasSite h r x.1.1=118 ∧ atlasSite w c x.1.2=118) :
    Holds (windowField pl H) (rootRow x y) := by
  simp only [Holds,rootRow,List.forall_mem_cons,List.not_mem_nil,
    CNF.Clause.eval,List.any_cons,List.any_nil,value]
  simp [window_root pl H x y root]

/-- A compressed price clause lists only the bits needed to force a
nonzero price. Its guard contains the literals that disable the clause
for other outgoing-arrow choices. -/
def priceRow {V : Type} (guard pattern : CNF.Clause (Wire V)) :
    CNF.Clause (Wire V) :=
  guard ++ pattern.map (fun (w,b) => (w,!b))

theorem eval_priceRow_iff {V : Type} (W : WindowField V)
    (guard pattern : CNF.Clause (Wire V)) :
    (priceRow guard pattern).eval (value W)=true ↔
      guard.eval (value W)=true ∨
      ¬(∀ w b, (w,b)∈pattern → value W w=b) := by
  simp only [priceRow,CNF.Clause.eval,List.any_append,Bool.or_eq_true,List.any_map]
  apply or_congr Iff.rfl
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨⟨w,b⟩,h,c⟩ all
    simp [all _ _ h] at c
  · intro h
    push Not at h
    obtain ⟨w,b,mem,ne⟩ := h
    refine ⟨(w,b),mem,?_⟩
    cases b <;> cases e : value W w <;> simp_all

/-- Soundness of a proposed compressed zero-price refutation clause.
The finite producer may choose the cube and how to compress it, but
the proof must show that the cube has no zero-price completion. -/
theorem physical_price_row {V : Type} (W : WindowField V)
    (guard pattern : CNF.Clause (Wire V)) (price : (Wire V → Bool) → Int)
    (clean : guard.eval (value W)≠true → price (value W)=0)
    (bad : ∀ a, (∀ w b, (w,b)∈pattern → a w=b) → price a≠0) :
    (priceRow guard pattern).eval (value W)=true := by
  apply (eval_priceRow_iff ..).mpr
  by_cases g : guard.eval (value W)=true
  · exact Or.inl g
  · exact Or.inr (fun h => bad _ h (clean g))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
