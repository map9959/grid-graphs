import GridGraphs.Constructions.CombRails
import GridGraphs.Core.ForcedMaximum

namespace GridGraphs.CombWord
open SimpleGraph

def cursor (j old : Nat) : Frontier := ⟨j%3,decide (j=0),old,[]⟩
def drawn (R : Nat) (w : List Nat) := lay (gridPort R) 0 start (rails R) w

private theorem fold_contains {V : Type*} (port : Nat → V) (es : List (Nat × Nat))
    (G : SimpleGraph V) :
    G ≤ es.foldl (insertPort port) G ∧ ∀ e ∈ es,
      edge (port e.1) (port e.2) ≤ es.foldl (insertPort port) G := by
  induction es generalizing G with
  | nil => simp
  | cons a es ih =>
    have h := ih (insertPort port G a)
    refine ⟨le_sup_left.trans h.1,?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact le_sup_right.trans h.1
    · exact h.2 e he

private theorem lay_le {V : Type*} (port : Nat → Nat → V) (w : List Nat)
    (j : Nat) (s : Frontier) (G : SimpleGraph V) : G ≤ lay port j s G w := by
  induction w generalizing j s G with
  | nil => rfl
  | cons m ms ih => exact (fold_contains _ _ _).1.trans (ih _ _ _)

private theorem at_column (R : Nat) (w : List Nat) (j old : Nat) (G : SimpleGraph Site)
    (i : Nat) (hi : i < w.length) (e : Nat × Nat)
    (he : e ∈ columnEdges (cursor (j+i) (if i=0 then old else w[i-1]!))
      w[i]) : edge (gridPort R (j+i) e.1) (gridPort R (j+i) e.2) ≤
        lay (gridPort R) j (cursor j old) G w := by
  induction w generalizing j old i G with
  | nil => simp at hi
  | cons m ms ih =>
    cases i with
    | zero =>
      simp at he
      rw [Nat.add_zero,lay]
      exact ((fold_contains _ _ _).2 e he).trans (lay_le _ ms _ _ _)
    | succ i =>
      have hl : i < ms.length := by simpa using hi
      have he' : e ∈ columnEdges (cursor ((j+1)+i) (if i=0 then m else ms[i-1]!)) ms[i] := by
        cases i <;> simpa [Nat.add_assoc,Nat.add_comm 1] using he
      have H := ih (j+1) m ((columnEdges (cursor j old) m).foldl
        (insertPort (gridPort R j)) G) i hl he'
      have cur : cursor (j+1) m = ⟨((cursor j old).phase+1)%3,false,m,[]⟩ := by
        simp [cursor,Nat.add_mod]
      simpa [lay,cur,Nat.add_assoc,Nat.add_comm 1] using H

private theorem cover {R : Nat} {w : List Nat} {i : Nat} (hi : i < w.length)
    {a b : Nat} (he : (a,b) ∈ columnEdges (cursor i (if i=0 then 0 else w[i-1]!)) w[i])
    (hne : gridPort R i a ≠ gridPort R i b) :
    (drawn R w).Adj (gridPort R i a) (gridPort R i b) := by
  have h := at_column R w 0 0 (rails R) i hi (a,b) (by simpa using he)
  have eq : lay (gridPort R) 0 (cursor 0 0) (rails R) w = drawn R w := by
    cases w <;> rfl
  simp only [Nat.zero_add,eq] at h
  exact h ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)

def Mark (R : Nat) (w : List Nat) (y x : Nat) : Prop :=
  y=0 ∨ y=R+7 ∨ (2≤y ∧ y≤R+1 ∧ x%3=0) ∨
    (R+2≤y ∧ y≤R+5 ∧ w[x]!.testBit (y-(R+2)))

private theorem baseAdj {R : Nat} {w : List Nat} {v z : Site}
    (ne : v ≠ z) (h : parent R v=z ∨ parent R z=v) : (drawn R w).Adj v z :=
  (lay_le _ w _ _ _) (show (rails R).Adj v z from ⟨ne,h⟩)

theorem horizontal {R y x : Nat} {w : List Nat} (hx : x+1 < w.length)
    (mark : Mark R w y x ∨ Mark R w y (x+1)) :
    (drawn R w).Adj (y,x+1) (y,x+2) := by
  by_cases cap : R+2≤y ∧ y≤R+5
  · let r := y-(R+2)
    have hr : r<4 := by dsimp [r]; omega
    have bits : w[x]!.testBit r ∨ w[x+1]!.testBit r := by
      simp only [Mark] at mark
      rcases mark with h|h <;> rcases h with h|h|h|h <;> first | omega | exact Or.inl h.2.2 | exact Or.inr h.2.2
    have he : (2+r,6+r) ∈ columnEdges (cursor (x+1) (if x+1=0 then 0 else w[x+1-1]!)) w[x+1] := by
      simp only [columnEdges,cursor, Id.run, pure, Nat.succ_ne_zero,decide_false, Bool.false_eq_true,
        ↓reduceIte,List.mem_append]
      right
      apply List.mem_map.mpr
      exact ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr hr,by
        simpa [getElem!_pos w (x+1) hx] using bits.symm⟩,rfl⟩
    have portOld : gridPort R (x+1) (2+r) = (y,x+1) := by
      simp [gridPort,show 2+r<6 by omega,show 2+r≠1 by omega]; dsimp [r]; omega
    have portNew : gridPort R (x+1) (6+r) = (y,x+2) := by
      simp [gridPort,show 6+r≠1 by omega,Nat.mod_eq_of_lt hr]; dsimp [r]; omega
    simpa only [portOld,portNew] using cover hx he
      (by rw [portOld,portNew]; simp : gridPort R (x+1) (2+r) ≠ gridPort R (x+1) (6+r))
  · apply baseAdj (by simp)
    simp only [Mark] at mark
    simp only [parent]
    split_ifs <;> simp_all <;> omega

theorem vertical {R y x : Nat} {w : List Nat} (hR : 0<R) (hx : x < w.length)
    (bound : y+1 ≤ R+7) (mark : Mark R w y x ∨ Mark R w (y+1) x) :
    (drawn R w).Adj (y,x+1) (y+1,x+1) := by
  by_cases top : y=R+1
  · subst y
    have hit : x%3=0 ∨ w[x].testBit 0 := by
      simp only [Mark,getElem!_pos w x hx] at mark
      rcases mark with h|h <;> rcases h with h|h|h|h <;> first
        | omega | exact Or.inl h.2.2 | exact Or.inr (by simpa using h.2.2)
    have he : (0,6) ∈ columnEdges (cursor x (if x=0 then 0 else w[x-1]!)) w[x] := by
      simp only [columnEdges,Id.run,pure,List.mem_append]
      left;left;left
      simpa [cursor] using hit
    exact cover hx he (by simp [gridPort])
  by_cases bot : y=R+5
  · subst y
    have hit : w[x].testBit 3 := by
      simp only [Mark,getElem!_pos w x hx] at mark
      rcases mark with h|h <;> rcases h with h|h|h|h <;> first
        | omega | exact (by simpa using h.2.2)
    have he : (1,9) ∈ columnEdges (cursor x (if x=0 then 0 else w[x-1]!)) w[x] := by
      simp only [columnEdges,Id.run,pure,List.mem_append]
      left;left;right; simp [hit]
    exact (cover hx he (R := R) (by simp [gridPort])).symm
  by_cases mid : R+2 ≤ y ∧ y<R+5
  · let r := y-(R+2)
    have hr : r<3 := by dsimp [r]; omega
    have hit : w[x].testBit r ∨ w[x].testBit (r+1) := by
      have h : y+1-(R+2)=r+1 := by dsimp [r]; omega
      simp only [Mark,getElem!_pos w x hx,h] at mark
      rcases mark with h|h <;> rcases h with h|h|h|h <;> first
        | omega | exact Or.inl h.2.2 | exact Or.inr h.2.2
    have he : (6+r,7+r) ∈ columnEdges (cursor x (if x=0 then 0 else w[x-1]!)) w[x] := by
      simp only [columnEdges,Id.run,pure,List.mem_append]
      left;right
      exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr hr,by simpa using hit⟩,rfl⟩
    have a : gridPort R x (6+r) = (y,x+1) := by
      simp [gridPort,show 6+r≠1 by omega,Nat.mod_eq_of_lt (show r<4 by omega)]
      dsimp [r]; omega
    have b : gridPort R x (7+r) = (y+1,x+1) := by
      rw [show 7+r=6+(r+1) by omega]
      simp [gridPort,show 6+(r+1)≠1 by omega,Nat.mod_eq_of_lt (show r+1<4 by omega)]
      dsimp [r]; omega
    simpa only [a,b] using cover hx he
      (by rw [a,b]; simp : gridPort R x (6+r) ≠ gridPort R x (7+r))
  · apply baseAdj (by simp)
    simp only [Mark] at mark
    by_cases zero : y=0
    · subst y; right; simp [parent]
    by_cases last : y=R+6
    · subst y; left; simp [parent]
    right
    have h : y+1≤R+1 ∧ x%3=0 := by omega
    simp [parent,last,zero,h.1,
      show (x+1)%3=1 by omega]

noncomputable def markedSet (R n : Nat) (w : List Nat) : Finset (GridVertex n n) := by
  classical
  exact Finset.univ.filter fun v => Mark R w v.1.val v.2.val

theorem markedSet_feasible {R n : Nat} {w : List Nat} (hR : 0<R) (hn : n=R+8)
    (hlen : w.length=n) (ok : (run start w).isSome) :
    markedSet R n w ∈ acyclicForcedSets n n := by
  classical
  apply mem_acyclicForcedSets.mpr
  let f (v : GridVertex n n) : Site := (v.1.val,v.2.val+1)
  apply (physical_sweep_acyclic R w ok).comap ⟨f,?_⟩ ?_
  · intro u v e
    obtain ⟨eu,em⟩ := e
    simp only [Finset.mem_coe,markedSet,Finset.mem_filter,Finset.mem_univ,true_and] at em
    rcases u with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
    rcases v with ⟨⟨b,hb⟩,⟨a,ha⟩⟩
    change ((Fin.mk y hy = Fin.mk b hb ∧ (x+1=a ∨ a+1=x)) ∨
      (Fin.mk x hx = Fin.mk a ha ∧ (y+1=b ∨ b+1=y))) at eu
    change Mark R w y x ∨ Mark R w b a at em
    change (drawn R w).Adj (y,x+1) (b,a+1)
    rcases eu with ⟨eq,hd⟩|⟨eq,hd⟩
    · have := Fin.mk.inj eq; subst b
      rcases hd with rfl|rfl
      · exact horizontal (by omega) em
      · exact (horizontal (by omega) em.symm).symm
    · have := Fin.mk.inj eq; subst a
      rcases hd with rfl|rfl
      · exact vertical hR (by omega) (by omega) em
      · exact (vertical hR (by omega) (by omega) em.symm).symm
  · intro a b eq
    change (a.1.val,a.2.val+1)=(b.1.val,b.2.val+1) at eq
    exact Prod.ext (Fin.ext (Prod.mk.inj eq).1) (Fin.ext (by have := (Prod.mk.inj eq).2; omega))

end GridGraphs.CombWord
