import GridGraphs.ResidueTwoUpper.OneGap.FanSeed
import GridGraphs.ResidueTwoUpper.OneGap.FanCap

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open L7 ResidueZero Stencil BoundarySix.Connected

/-- The mark bits of the seed give an actual path to *its* north tooth.
The crop endpoint is at depth five, even in the first tile after the
isolate where the bit at depth five itself need not be set. -/
theorem rooted_seed (u j : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (w : View) (s f : Bool) (side : rim F w s f) (lo : 3≤j) (hi : j<33+42*u)
    (seven : tile F w 1 j=72) (more : lane (tile F w 4 j) 0=1) :
    let atR := siteAt u j (by omega) w
    ∃ (a : PerimeterVertex (35+42*u)) (src dst : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p}),
      a.1=atR 0 ∧ src.1=atR 1 ∧ dst.1=atR 5 ∧ (Bonds F).Adj src.1 a.1 ∧
      ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src dst := by
  let X := chartCol F w
  have grab : ∀ a b c : Fin 128, window a b c 1=72 → lane (window a b c 4) 0=1 →
      lane a 2=1 ∧ lane a 3=1 ∧ lane a 4=1 := by native_decide
  obtain ⟨h2,h3,h4⟩ := grab ⟨_,col_lt F w j⟩ ⟨_,col_lt F w (j+1)⟩ ⟨_,col_lt F w (j+2)⟩ seven more
  let R := siteAt u j (by omega) w
  have geom := geometry u j (by omega) w
  have mem (r : Fin 7) (h : lane (X j) r=1) : R r∈F := by
    change lane (chartCol F w j) r=1 at h
    rw [col_bit,←show coord (R r)=_ from coord_onSite ..,marked_at] at h; simpa using h
  have footmark : R 0∈F := by
    have h := side 0 j (by decide) (by omega) true (by simp [preset,show j≠1 by omega,show j≠2 by omega,show j+2≠35+42*u by omega])
    have pos : coord (R 0)=L7.view w (35+42*u:Nat) 0 j := by
      exact coord_onSite ..
    simp only [Nat.cast_zero] at h
    rw [←pos,marked_at] at h
    exact of_decide_eq_true h
  let I (k : Fin 6) : {p : GridVertex (35+42*u) (35+42*u) // ¬IsGridBoundary p} :=
    ⟨R ⟨k.val+1,by have := k.isLt; omega⟩,fun h => Nat.succ_ne_zero _ ((geom _).1.mp h)⟩
  let G := (Bonds F).induce {p | ¬IsGridBoundary p}
  have e12 : G.Adj (I 0) (I 1) := ⟨(geom 1).2 2 rfl,Or.inr (mem 2 h2)⟩
  have e23 : G.Adj (I 1) (I 2) := ⟨(geom 2).2 3 rfl,Or.inr (mem 3 h3)⟩
  have e34 : G.Adj (I 2) (I 3) := ⟨(geom 3).2 4 rfl,Or.inr (mem 4 h4)⟩
  have e45 : G.Adj (I 3) (I 4) := ⟨(geom 4).2 5 rfl,Or.inl (mem 4 h4)⟩
  exact ⟨⟨_,(geom 0).1.mpr rfl⟩,I 0,I 4,rfl,rfl,rfl,⟨((geom 0).2 1 rfl).symm,Or.inr footmark⟩,
    e12.reachable.trans (e23.reachable.trans (e34.reachable.trans e45.reachable))⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
