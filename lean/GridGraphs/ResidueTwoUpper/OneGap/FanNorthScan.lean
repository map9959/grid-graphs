import GridGraphs.ResidueTwoUpper.OneGap.FanShrink

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSlab FanSweep

/-- Physical rows 1–18: includes the birth sites above the shrinking slab. -/
def north (q y i : Nat) := if y=0 then
  if i=0 then 16 else if i+1<q then 48 else if i<q then 16 else if i=q then 4 else 6
  else actual q y i

def northGoal (h : Nat) (G : Grid) := (List.range 6).all fun y => (List.range (57+h)).all fun k =>
  (cell G (3*y) (3*k)).all fun m => m==transpose (north 57 y k)
private theorem checkedNorth : ∀ h∈[2,4,6,8], check (box h) (northGoal h) 32 (base h) := by native_decide

theorem north_output (h : Nat) (hh : h∈[2,4,6,8]) (T : Path (box h)) (init : Kept T (base h))
    (j y k : Nat) (hj : j≤T.last) (hy : y<6) (hk : k<57+h) (label : T.col j=3*k) :
    T.M (3*y) j=transpose (north 57 y k) := by
  obtain ⟨G,end',live⟩ := sound T _ 32 _ init (checkedNorth h hh)
  have z := live (3*y) (by change 3*y≤27; omega) j hj
  rw [label] at z
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp end' y (List.mem_range.mpr hy)) k (List.mem_range.mpr hk)) _ z)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
