import GridGraphs.ResidueTwoUpper.OneGap.FanSeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 GridGraphs.ResidueTwoUpper.Exceptional.Frame

-- Restrict the three planted columns before quantifying over the two
-- open columns. This 7-by-5 test needs neither ports nor root tags.
private theorem move : ∀ j : Fin 33, 3≤j.val → j.val≤27 → j.val%3=0 →
    ∀ b c d : Fin 16, ∀ a : Fin 128,
    cleanBand j a (64+b.val) (64+c.val) →
    cleanBand (j+1:Nat) (64+b.val) (64+c.val) (64+d.val) →
    ∀ e : Fin 128, cleanBand (j+2:Nat) (64+c.val) (64+d.val) e →
    window (64+b.val) (64+c.val) (64+d.val) 1=448 := by native_decide

/-- The final stripe propagation up to the true fringe. In this chart
rows are counted *inward from the receiving side*; hence 448 encodes the
stripe that is 7 in the fan convention. All five columns are physical. -/
theorem fringe_step (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (zs : ∀ p,patchSlack F p=0) (w : View) (j : Nat)
    (lo : 3≤j) (hi : j+6≤33+42*u) (phase : j%3=0) (seed : tile F w 4 (j+1)=448) :
    tile F w 1 (j+1)=448 := by
  let X := chartCol F w
  have fold' : ∀ k≤2, fold u (j+k)=fold u j+k := by
    intro k hk; unfold fold; split_ifs <;> omega
  have B (k : Nat) (hk : k≤2) := physical u F acy zs w (j+k) (by omega)
  have three (k : Nat) (hk : k≤2) : cleanBand (fold u j+k) (X (j+k)) (X (j+k+1)) (X (j+k+2)) := by
    rw [←fold' k hk]; exact B _ hk
  have bound (k : Nat) : X k<128 := col_lt ..
  have narrow : ∀ a b c : Fin 128, window a b c 4=448 →
      (64≤a.val ∧ a.val<80) ∧ (64≤b.val ∧ b.val<80) ∧ (64≤c.val ∧ c.val<80) := by native_decide
  obtain ⟨ab,ac,ad⟩ := narrow ⟨_,bound (j+1)⟩ ⟨_,bound (j+2)⟩ ⟨_,bound (j+3)⟩ seed
  dsimp only at ab ac ad
  let J : Fin 33 := ⟨fold u j,by unfold fold; split_ifs <;> omega⟩
  have hj : 3≤J.val ∧ J.val≤27 ∧ J.val%3=0 := by dsimp [J,fold]; split_ifs <;> omega
  let b : Fin 16 := ⟨X (j+1)-64,by omega⟩
  let c : Fin 16 := ⟨X (j+2)-64,by omega⟩
  let d : Fin 16 := ⟨X (j+3)-64,by omega⟩
  have H := move J hj.1 hj.2.1 hj.2.2 b c d ⟨_,bound j⟩
  have eb : 64+b.val=X (j+1) := by dsimp [b]; omega
  have ec : 64+c.val=X (j+2) := by dsimp [c]; omega
  have ed : 64+d.val=X (j+3) := by dsimp [d]; omega
  rw [eb,ec,ed] at H
  exact H (three 0 (by decide)) (three 1 (by decide)) ⟨_,bound (j+4)⟩ (three 2 (by decide))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
