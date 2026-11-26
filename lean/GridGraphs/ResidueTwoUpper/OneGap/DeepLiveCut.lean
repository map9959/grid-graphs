import GridGraphs.ResidueTwoUpper.OneGap.ShortBirthCut

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.DeepCut
open ResidueZero Stencil L7 FanSlab Short FanSeed EastBoundary BoundarySix.Connected SouthCap

def fits (k q : Nat) := Guarded.atCut k q (q/6) (q+2-3*(q/6)+1)

/-- Restart the eastern-word induction inside the long fan. On its last
row only the plain suffix is needed, even if the full history word has
already lost its middle segment. -/
theorem front {u F w q P} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic) (big : 57≤q)
    (old : Front F w q (11+14*u) ((q-15)/6+2) (q-3*((q-15)/6)+3)) :
    let y := q/6; let b := q+2-3*y
    Front F w q (11+14*u) y (b+1) ∧ Plateau F w y y b (11+14*u) := by
  intro y b
  let z := (q-15)/6
  have room := S.room
  have mid : 6*y≤q := by dsimp [y]; omega
  have off : b+3*y=q+2 := by dsimp [b]; omega
  have yl : z+2≤y := by dsimp [z,y]; omega
  have R := north_rows north_output u q big room S.odd F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) S.west
    (by rw [tile_eq F w (by omega)]; exact S.paid)
    (fun i lo hi => by rw [tile_eq F w (by omega)]; exact S.east i lo hi)
  have row {j i : Nat} (jl : 2≤j) (jh : j≤y) (il : 3*j+1 ≤ i) (ih : i<11+14*u) :=
    rows_restart S acy (.inr ⟨rfl,by omega⟩) (start:=z+2) (.inr (by dsimp [z]; omega))
      (fun r rl rh _ c cl ch => LiveCut.read_edge (R r (by dsimp [z] at *; omega))
        (by omega) (by dsimp [z] at *; omega) cl ch) j jl (by omega) i il ih
  have plain {i} (lo : b ≤ i) (hi : i<11+14*u) : maskAtTile F w y i=73 := by
    rw [row (by omega) le_rfl (by omega) hi]; unfold edge; split_ifs <;> omega
  have guard : Plateau F w y y b (11+14*u) := by
    intro j jl jh i il ih; rw [show j=y by omega]; exact plain il ih
  refine ⟨⟨fun j l h i il ih => guard j l h i (by omega) ih,?_,?_⟩,guard⟩
  · intro t tl th rt
    apply dangling_of_marks _ q y t (by omega) (by omega) (by omega) rt
    intro j jh i a e near it ti bound al el m
    by_cases endrow : j=y
    · subst j
      have v := plateau_bit (plain (i:=i) (by omega) (by omega)) ⟨a,al⟩ ⟨e,el⟩
      rw [m] at v
      have az : a=0 := by by_contra! h; simp [h] at v
      unfold NorthFanLines.mark; omega
    apply right_bits q j i a e al el (by omega) (by omega)
    by_cases prev : j<z+2
    · have eq := R j (by dsimp [z] at *; omega) i a e bound al el
      rw [m] at eq; exact eq.symm
    have mask := row (j:=j) (i:=i) (by omega) jh (by omega) (by omega)
    have eq := LiveCut.eastern (q:=q) (j:=j) (i:=i) (by omega) (by omega) (by omega)
    have read := ShortBirth.mark_read (m:=history q j i) (by
      rw [eq,mask]; unfold edge LiveCut.mword; split_ifs <;> rfl)
      (by rw [eq]; unfold LiveCut.mword; split_ifs <;> decide) al el
    rw [m] at read; exact read.symm
  · intro i il ih rt
    have grow (j : Nat) (lo : z+2≤j) (hi : j≤y) : RootLine F w i j := by
      induction j,lo using Nat.le_induction with
      | base => exact old.2.2 i (by dsimp [z] at *; omega) ih rt
      | succ j _ prior =>
        have tooth : Strip.GridScan.Rooted.tile F w j i=73 := by
          rw [show Strip.GridScan.Rooted.tile F w j i=edge (q+2-3*j) i from
            row (by omega) (by omega) (by omega) ih]; unfold edge; split_ifs <;> omega
        apply Strip.GridScan.Rooted.extend_line (prior (by omega))
        · rw [tooth]; decide
        · left; rw [tooth]; decide
    exact grow _ yl le_rfl

theorem exclude {u F w q P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (big : 57≤q) (ok : fits (11+14*u) q)
    (old : Front F w q (11+14*u) ((q-15)/6+2) (q-3*((q-15)/6)+3)) : False := by
  obtain ⟨fr,guard⟩ := front S acy big old
  have room := S.room
  exact Guarded.exclude_from H acy one score (by omega) room (y:=q/6) (f:=q+2-3*(q/6)+1)
    ok (by omega) (by omega) (by push_cast; omega) fr (by simpa using guard)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.DeepCut
