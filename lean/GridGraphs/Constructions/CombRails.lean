import GridGraphs.Constructions.CombSweep

namespace GridGraphs.CombWord
open SimpleGraph

abbrev Site := Nat × Nat

/-- The board occupies columns 1..n; column zero provides four unused
initial ports. R is the number of pitch rows between row 1 and the cap. -/
def parent (R : Nat) (v : Site) : Site :=
  let (y,x) := v
  if y=0 ∨ y=R+7 then (y,x-1)
  else if y=1 then (0,x)
  else if y≤R+1 then
    if x%3=1 then (y-1,x) else if x%3=2 then (y,x-1) else (y,x+1)
  else if y=R+6 then (R+7,x) else v

def rails (R : Nat) := SimpleGraph.fromRel (fun v w => parent R v = w)

def height (R : Nat) (v : Site) :=
  let (y,x) := v
  if y=R+7 then x else if y=R+6 then x+1 else
    x+4*y+(if 2≤y ∧ x%3≠1 then 2 else 0)

theorem parent_down (R : Nat) (v : Site) (h : parent R v ≠ v) :
    height R (parent R v) < height R v := by
  rcases v with ⟨y,x⟩
  simp only [parent] at *
  split_ifs at h ⊢ <;> simp_all [height] <;> split_ifs <;> omega

theorem rails_forest (R : Nat) : (rails R).IsAcyclic := by
  classical
  intro u c cyc
  obtain ⟨v,hv,hm⟩ := c.support.toFinset.exists_max_image (height R)
    ⟨u,by simp⟩
  have mem := List.mem_toFinset.mp hv
  let d := c.rotate v mem
  have hd : d.IsCycle := cyc.rotate _
  have maxAt (i : Nat) : height R (d.getVert i) ≤ height R v :=
    hm _ (List.mem_toFinset.mpr ((c.mem_support_rotate_iff v mem).mp (d.getVert_mem_support i)))
  have down {z : Site} (e : (rails R).Adj v z) (le : height R z ≤ height R v) :
      parent R v = z := by
    rcases e.2 with h | h
    · exact h
    · have := parent_down R z (by rw [h]; exact e.ne)
      rw [h] at this
      omega
  exact hd.snd_ne_penultimate ((down (d.adj_snd hd.not_nil) (maxAt 1)).symm.trans
    (down (d.adj_penultimate hd.not_nil).symm (maxAt _)))

theorem reachable_parent (R : Nat) (v : Site) : (rails R).Reachable v (parent R v) := by
  by_cases h : v = parent R v
  · rw [← h]
  · exact (show (rails R).Adj v (parent R v) from ⟨h,Or.inl rfl⟩).reachable

theorem upper_root (R y x : Nat) (hy : y ≤ R+1) :
    (rails R).Reachable (y,x) (0,0) := by
  apply (reachable_parent R _).trans
  by_cases h : parent R (y,x) = (y,x)
  · have eq : y=0 ∧ x=0 := by
      simp only [parent] at h
      split_ifs at h <;> simp_all <;> omega
    rw [h,eq.1,eq.2]
  · exact upper_root R _ _ (by
      change (parent R (y,x)).1 ≤ R+1
      simp only [parent]; split_ifs <;> simp_all; omega)
termination_by height R (y,x)
decreasing_by exact parent_down R _ h

def gridPort (R j i : Nat) : Site :=
  if i=0 then (R+1,j+1) else if i=1 then (R+6,j+1) else if i<6 then
    (R+i,j) else (R+2+(i-6)%4,j+1)

private theorem cap_isolated (R y x : Nat) (lo : R+2 ≤ y) (hi : y ≤ R+5)
    (v : Site) : ¬(rails R).Adj (y,x) v := by
  rintro ⟨ne,h|h⟩
  · simp [parent,show y≠0 by omega,show y≠R+7 by omega,show y≠1 by omega,
      show ¬ y≤R+1 by omega,show y≠R+6 by omega] at h
    exact ne h
  · rcases v with ⟨b,c⟩
    simp only [parent] at h
    split_ifs at h <;> simp_all <;> omega

def layout (R : Nat) : RailLayout Site (rails R) where
  port := gridPort R
  fresh j := by
    have new (r : Fin 4) : gridPort R j (6+r.val) = (R+2+r.val,j+1) := by
      simp [gridPort,Nat.mod_eq_of_lt r.isLt]; omega
    constructor
    · intro i hi r; rw [new]
      interval_cases i <;> simp [gridPort] <;> omega
    · intro r s h
      simp only [new,Prod.mk.injEq] at h
      exact Fin.ext (by omega)
    · intro r v; rw [new]; exact cap_isolated _ _ _ (by omega) (by omega) v
  future j l lt i r := by
    simp only [gridPort]; split_ifs <;> simp_all <;> omega
  shift j i hi := by
    interval_cases i
    · exact (upper_root R _ _ le_rfl).trans (upper_root R _ _ le_rfl).symm
    · change (rails R).Reachable (R+6,j+2) (R+6,j+1)
      have down (c : Nat) : (rails R).Reachable (R+6,c) (R+7,c) := by
        simpa [parent] using reachable_parent R (R+6,c)
      refine (down _).trans (Reachable.trans ?_ (down _).symm)
      simpa [parent] using reachable_parent R (R+7,j+2)
    all_goals apply Reachable.refl

theorem initial_labels (R : Nat) :
    ExtendsLabels (rails R) (gridPort R 0) start.parts := by
  let c : Site → Nat := fun (y,_) =>
    if y ≤ R+1 then 0 else if R+6 ≤ y then 1 else y-R
  have same (v : Site) : c (parent R v) = c v := by
    rcases v with ⟨y,x⟩
    simp only [parent,c]
    split_ifs <;> simp_all; omega
  refine ⟨c,?_,?_⟩
  · intro v w e
    rcases e.2 with h|h
    · rw [←h]; exact (same v).symm
    · rw [←h]; exact same w
  · intro i a hi
    have b := (List.getElem?_eq_some_iff.mp hi).1
    change i < 6 at b
    interval_cases i <;> simp [start] at hi <;> subst a <;>
      simp [gridPort,c]

theorem physical_sweep_acyclic (R : Nat) (w : List Nat) (ok : (run start w).isSome) :
    (lay (gridPort R) 0 start (rails R) w).IsAcyclic :=
  accepted_layout_forest (layout R) (rails_forest R) (initial_labels R) ok

end GridGraphs.CombWord
