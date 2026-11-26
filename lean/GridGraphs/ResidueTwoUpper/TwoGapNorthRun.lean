import GridGraphs.ResidueTwoUpper.TwoGapNorthReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero

def tag (u j : Nat) := if j<23 then j else if j<23+42*u then 23+(j-23)%3 else j-42*u
private theorem tag_step (u j : Nat) : tag u (j+1)=tag u j+1 ∨ tag u j=25 ∧ tag u (j+1)=23 := by
  unfold tag; split_ifs <;> omega

/-- There is no scan trace at any exceptional width. The inclusion at
the periodic seam is enough; no repeated choice of physical masks or
arrows is assumed. -/
theorem no_trace (u : Nat) (X : Nat → State) (init : X 0∈reach 0)
    (steps : ∀ j<35+42*u, X (j+1)∈next (tag u j) (X j)) : False := by
  have ck := checked; simp only [Bool.and_eq_true] at ck; obtain ⟨loop,done⟩ := ck
  have visit (j : Nat) (hj : j≤35+42*u) : X j∈reach (tag u j) := by
    induction j with
    | zero => simpa [tag] using init
    | succ j ih =>
      have step : X (j+1)∈reach (tag u j+1) :=
        List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨_,ih (by omega),steps j (by omega)⟩)
      rcases tag_step u j with eq|⟨end',start⟩
      · rwa [eq]
      · rw [end'] at step; rw [start]
        exact List.contains_iff_mem.mp (List.all_eq_true.mp loop _ step)
  have m := visit _ le_rfl
  rw [show tag u (35+42*u)=35 by unfold tag; split_ifs <;> omega] at m
  have z : reach 35=[] := List.isEmpty_iff.mp done
  simp [z] at m

-- Local sufficient conditions for one transition: raw physical compass
-- arrows of six sites, accounting only for horizontal and vertical bonds
-- internal to the strip.
theorem owners_sound (j a b c west : Nat) (d : Nat → Nat) (w : Nat → Nat)
    (base : w 0=0)
    (dom : ∀ r<6, d r∈dirs j r a b c)
    (left : ∀ r<6, (d r==2)=(bit west r==1))
    (vert : ∀ r<6, (decide (r>0) && (d (r-1)==1)).toNat+(d r==3).toNat=
      (r != 0 && decide (bit b r+bit b (r-1)>0)).toNat)
    (east : ∀ r<6, d r=0 → j≠34 ∧ bit b r+bit c r>0)
    (sum : ∀ r<6, w (r+1)=w r+(if j != 34 && (bit b r+bit c r>0) && d r != 0 then 2^r else 0)) :
    w 6∈owners j a b c west := by
  let phase (r : Nat) := (decide (r>0) && (d (r-1)==1),w r)
  let run (r : Nat) := (List.range r).foldl (fun states i => states.flatMap (rowStep j a b c west i)) [(false,0)]
  have step (r : Nat) (hr : r<6) : phase (r+1)∈rowStep j a b c west r (phase r) := by
    apply List.mem_filterMap.mpr
    refine ⟨_,dom r hr,?_⟩
    dsimp [phase]; simp only [left r hr,vert r hr,sum r hr,ne_eq,beq_self_eq_true,Bool.not_true,
      bne_self_eq_false,ite_false,↓reduceDIte]
    by_cases e : d r=0
    · obtain ⟨nj,h⟩ := east r hr e
      simp [e,nj,h]
    · simp [e]
  have go (r : Nat) (hr : r≤6) : phase r∈run r := by
    induction r with
    | zero => simp [phase,run,base]
    | succ r ih =>
      change phase (r+1)∈(List.range (r+1)).foldl _ _
      rw [List.range_succ,List.foldl_append]; exact List.mem_flatMap.mpr ⟨_,ih (by omega),step r (by omega)⟩
  exact List.mem_map.mpr ⟨phase 6,go _ le_rfl,rfl⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
