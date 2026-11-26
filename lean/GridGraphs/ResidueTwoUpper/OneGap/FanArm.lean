import GridGraphs.ResidueTwoUpper.OneGap.L7Exclusion

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected

private theorem inject (w : View) (N r j a b : Int) (h : L7.view w N r j=L7.view w N a b) : r=a ∧ j=b := by
  cases w with | mk x y s => cases x <;> cases y <;> cases s <;> simp [L7.view,reflect] at h <;> omega

private def undo (v : View) (N : Int) (p : Pos) : Pos :=
  let z := (reflect v.rowFar N p.1,reflect v.colFar N p.2)
  if v.swap then z.swap else z
private theorem inverse (v : View) (N : Int) (p : Pos) :
    L7.view v N (undo v N p).1 (undo v N p).2=p := by
  cases v with | mk x y s => cases x <;> cases y <;> cases s <;> ext <;> simp [L7.view,reflect,undo]
private theorem phase (v : View) (u : Nat) (p : Pos)
    (h : arm (35+42*(u:Int)) p.1 p.2 ∨ arm (35+42*(u:Int)) p.2 p.1) :
    let z := undo v (35+42*(u:Int)) p
    arm (35+42*(u:Int)) z.1 z.2 ∨ arm (35+42*(u:Int)) z.2 z.1 := by
  cases v with | mk x y s => cases x <;> cases y <;> cases s <;> simp [undo,reflect,arm] at * <;> omega

/-- Relative to the unique gap corner, a phase-five star must lie on one
of its two incident arms. The far-corner fringe is included, even when
its first visible star is at transverse index five. -/
theorem near_arm (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (P : GridVertex (35+42*u) (35+42*u) → _)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (p : GridVertex (35+42*u) (35+42*u))
    (h : arm (35+42*(u:Int)) (coord p).1 (coord p).2 ∨ arm (35+42*(u:Int)) (coord p).2 (coord p).1)
    (zero : ∀ x, x≠Sum.inl p → weightAt F P x=0) (v : View) (f g : Bool)
    (west : rim F v false f) (east : rim F (turnView v) true g) :
    ∃ (w : View) (s t : Bool) (i : Nat), rim F w s t ∧
      coord p=L7.view w (35+42*(u:Int)) 2 ((i:Int)+1) ∧ 4≤ i ∧ i+5≤33+42*u ∧ i%6=4 := by
  let N : Int := 35+42*(u:Int)
  let z := undo v N (coord p)
  have loc : arm N z.1 z.2 ∨ arm N z.2 z.1 := phase v u _ h
  have eq : coord p=L7.view v N z.1 z.2 := (inverse ..).symm
  have give (w : View) (s t : Bool) (l : Int) (rw : rim F w s t) (a : arm N 2 l)
      (match' : coord p=L7.view w N 2 l) : ∃ (w : View) (s t : Bool) (i : Nat), rim F w s t ∧
      coord p=L7.view w N 2 ((i:Int)+1) ∧ 4≤ i ∧ i+5≤33+42*u ∧ i%6=4 := by
    refine ⟨w,s,t,(l-1).toNat,rw,?_,?_,?_,?_⟩ <;> unfold arm at a <;> dsimp [N] at a <;>
      first | convert match' using 2 <;> omega | omega
  by_cases a : z.1=2
  · have loc' : arm N 2 z.2 := by unfold arm at *; omega
    exact give v _ _ _ west loc' (by simpa [a] using eq)
  by_cases b : z.2=2
  · have loc' : arm N 2 z.1 := by unfold arm at *; omega
    exact give (turnView v) _ _ _ east loc' (by simpa [turned,b] using eq)
  exfalso; apply junction_false u F v f g west east
  intro w hw j hj
  apply local_band catalogue_checked u F acy P step (fun k => Or.inl (zero (.inr k) (by simp))) w j hj
  intro r hr active x hx
  apply zero (.inl x); intro contra; cases contra
  rw [eq] at hx
  rcases hw with rfl|rfl
  · obtain ⟨row,col⟩ := inject _ _ _ _ _ _ hx
    unfold arm at loc; dsimp only [N] at *; unfold fold at active; split_ifs at active <;> omega
  · rw [turned] at hx
    obtain ⟨row,col⟩ := inject _ _ _ _ _ _ hx
    unfold arm at loc; dsimp only [N] at *; unfold fold at active; split_ifs at active <;> omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
