import GridGraphs.NoPitch.PhysicalKeys

namespace GridGraphs.NoPitch.TailCoverage
open Keys

/-- Agreement of signed distances up to saturation at radius nine. -/
def Sat (a b : Int) := a=b ∨ (9 ≤ a ∧ 9 ≤ b) ∨ (a ≤  -9 ∧ b ≤  -9)

private theorem sat_neg {a b : Int} (h : Sat a b) : Sat (-a) (-b) := by
  unfold Sat at *; omega

private theorem sat_clip {a b : Int} (h : Sat a b) : clip a = clip b := by
  unfold Sat clip at *; omega

/-- The parameters `l,m` are last valid coordinates, not widths. -/
structure Axis (l m z t : Nat) : Prop where
  src : z  ≤  l
  dst : t  ≤  m
  residue : z%3=t%3
  low : Sat z t
  high : Sat (l-z : Nat) (m-t : Nat)

structure Match (l m i j a b : Nat) : Prop where
  row : Axis l m i a
  col : Axis l m j b
  diff : Sat ((i:Int)-j) ((a:Int)-b)
  anti : Sat ((i:Int)+j-l) ((a:Int)+b-m)

private theorem Axis.flip {l m z t} (h : Axis l m z t) (w : l=m+6) :
    Axis l m (l-z) (m-t) := by
  rcases h with ⟨h₁,h₂,h₃,h₄,h₅⟩
  refine ⟨by omega,by omega,by omega,h₅,?_⟩
  simpa [Nat.sub_sub_self h₁,Nat.sub_sub_self h₂] using h₄

private theorem Match.swap {l m i j a b} (h : Match l m i j a b) :
    Match l m j i b a := by
  refine ⟨h.col,h.row,?_,?_⟩
  · convert sat_neg h.diff using 1 <;> omega
  · simpa [add_comm] using h.anti

private theorem Match.flipCol {l m i j a b} (h : Match l m i j a b) (w : l=m+6) :
    Match l m i (l-j) a (m-b) := by
  have := h.col.src; have := h.col.dst
  refine ⟨h.row,h.col.flip w,?_,?_⟩
  · convert h.anti using 1 <;> omega
  · convert h.diff using 1 <;> omega

private theorem Match.flipRow {l m i j a b} (h : Match l m i j a b) (w : l=m+6) :
    Match l m (l-i) j (m-a) b := (h.swap.flipCol w).swap

private theorem canonical {m i j : Nat} (hm : 57 ≤ m) (ij : i ≤ j) (hj : 2*j ≤ m+6) :
    ∃ a b, Match (m+6) m i j a b := by
  by_cases hi : 12 ≤ i
  · refine ⟨i-3,j-3,?_,?_,?_,?_⟩
    all_goals first | (unfold Sat; omega) | (constructor <;> (try unfold Sat) <;> omega)
  · by_cases gap : i+12 ≤ j
    · refine ⟨i,j-3,?_,?_,?_,?_⟩
      all_goals first | (unfold Sat; omega) | (constructor <;> (try unfold Sat) <;> omega)
    · refine ⟨i,j,?_,?_,?_,?_⟩
      all_goals first | (unfold Sat; omega) | (constructor <;> (try unfold Sat) <;> omega)

/-- Every point on the larger board has an indistinguishable centre on the
smaller one. Fold into the ordered octant, compress there, then unfold. -/
theorem representative {m i j : Nat} (hm : 57 ≤ m) (hi : i ≤ m+6) (hj : j ≤ m+6) :
    ∃ a b, Match (m+6) m i j a b := by
  have lower (u v : Nat) (hu : 2*u ≤ m+6) (hv : 2*v ≤ m+6) :
      ∃ a b, Match (m+6) m u v a b := by
    by_cases h : u ≤ v
    · exact canonical hm h hv
    · obtain ⟨a,b,e⟩ := canonical hm (by omega : v ≤ u) hu
      exact ⟨b,a,e.swap⟩
  have rows (u : Nat) (hu : 2*u ≤ m+6) : ∃ a b, Match (m+6) m u j a b := by
    by_cases h : 2*j ≤ m+6
    · exact lower u j hu h
    · obtain ⟨a,b,e⟩ := lower u (m+6-j) hu (by omega)
      exact ⟨a,m-b,by simpa [Nat.sub_sub_self hj] using e.flipCol rfl⟩
  by_cases h : 2*i ≤ m+6
  · exact rows i h
  · obtain ⟨a,b,e⟩ := rows (m+6-i) (by omega)
    exact ⟨m-a,b,by simpa [Nat.sub_sub_self hi] using e.flipRow rfl⟩

private theorem Axis.key {l m z t} (h : Axis l m z t) :
    axis (l+1) 8 z = axis (m+1) 8 t := by
  rcases h with ⟨_,_,_,h₁,h₂⟩
  unfold Sat at h₁ h₂
  unfold axis
  repeat
    split
    all_goals try omega

private theorem Match.key {l m i j a b} (h : Match l m i j a b) :
    fine (l+1) 8 i j = fine (m+1) 8 a b := by
  simp only [fine,h.row.key,h.col.key,Nat.cast_add,Nat.cast_one]
  have hd := sat_clip h.diff
  have ha := sat_clip h.anti
  simp only [show (i:Int)+j+1-(l+1)=i+j-l by omega,
    show (a:Int)+b+1-(m+1)=a+b-m by omega,hd,ha]

theorem Match.view {l m i j a b} (h : Match l m i j a b) (w : l=m+6) (g : Fin 8) :
    let p := transform g (l+1) i j
    let q := transform g (m+1) a b
    fine (l+1) 8 p.1 p.2 = fine (m+1) 8 q.1 q.2 := by
  have := h.col.src; have := h.col.dst
  fin_cases g <;> simp [transform,Nat.sub_sub_self h.col.src,Nat.sub_sub_self h.col.dst] <;>
    first | exact h.key | exact h.swap.key | exact (h.flipRow w).key |
      exact (h.flipCol w).key | exact ((h.flipRow w).flipCol w).key |
      exact (h.swap.flipRow w).key | exact (h.swap.flipCol w).key |
      exact ((h.swap.flipRow w).flipCol w).key

end GridGraphs.NoPitch.TailCoverage
