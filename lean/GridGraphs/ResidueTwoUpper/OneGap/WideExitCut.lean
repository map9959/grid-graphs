import GridGraphs.ResidueTwoUpper.OneGap.ShortBirthCut
import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryExit

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.WideExitCut
open ResidueZero Stencil L7 FanSlab FanSeed Short EastBoundary BoundarySix.Connected SouthCap

set_option maxHeartbeats 750000 in
/-- A low head (9 or 73) seals the same dangling tips as a plain
guard: both masks have marks only in their first column. The wider
exit additionally forces the guard itself to be plain. -/
theorem front {u F P w q y x} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (big : 35≤q) (room : q+6≤11+14*u) (yl : 4≤y)
    (fan : 6*y+3≤q) (off : q+2=x+8+3*y) :
    Front F w q (11+14*u) (y+1) (x+6) ∧ (6*y+4≤q → Plateau F w (y+1) (y+1) (x+5) (11+14*u)) := by
  have row {j i : Nat} (jl : 2≤j) (jh : j≤y) (il : 3*j+1 ≤ i) (ih : i<11+14*u) :=
    rows_restart S acy (.inr ⟨rfl,big⟩) (start:=2) (.inr (by omega)) (by intro r l h; omega)
      j jl (by omega) i il ih
  have roots (i : Nat) (rt : q < i) (hi : i<11+14*u) : RootLine F w i (y+1) := by
    have tooth : Strip.GridScan.Rooted.tile F w y i=73 := by
      rw [show Strip.GridScan.Rooted.tile F w y i=edge (q+2-3*y) i from row (by omega) le_rfl (by omega) hi]
      unfold edge; split_ifs <;> omega
    apply Strip.GridScan.Rooted.extend_line (ShortBirth.north_roots S acy (.inr ⟨rfl,big⟩)
      (by omega) (by omega) yl (by omega) rt hi)
    · rw [tooth]; decide
    · left; rw [tooth]; decide
  have head := exit_head S acy (by omega) big fan room off
  have plain := Departure.plainBeyond H acy one score hk (r:=y+1) (c:=x+5)
    (by omega) (by omega) (by omega) (by omega) head (roots _ (by omega) (by omega))
  have guard : 6*y+4≤q → Plateau F w (y+1) (y+1) (x+5) (11+14*u) := by
    intro wide j lo hi i il ih; rw [show j=y+1 by omega]
    rcases Nat.eq_or_lt_of_le il with rfl|lt
    · obtain ⟨a,b,e⟩ := wide_exit_tiles S acy (by omega) big wide room off
      exact Departure.pair_plain H acy one score hk (r:=y+1) (c:=x+3)
        (by omega) (by omega) (by omega) (by omega) a b e (roots _ (by omega) (by omega))
    · exact plain i lt ih
  refine ⟨⟨fun j lo hi i il ih => (show j=y+1 by omega) ▸ plain i (by omega) ih,?_,fun i _ hi rt => roots i rt hi⟩,guard⟩
  intro t tl th rt
  apply dangling_of_marks _ q (y+1) t (by omega) (by omega) (by omega) rt
  intro j jh i a b near it ti _ al bl hm
  by_cases endrow : j=y+1
  · subst j
    have modes : maskAtTile F w (y+1) i=9 ∨ maskAtTile F w (y+1) i=73 := by
      by_cases e : i=x+5
      · rw [e]; exact head
      · exact .inr (plain i (by omega) (by omega))
    have az : a=0 := by
      rcases modes with nine|yes
      · have v := ShortBirth.mark_read (j:=y+1) (i:=i) (F:=F) (w:=w) (m:=3) nine (by decide) al bl
        rw [hm] at v
        have tab : ∀ s t : Fin 3, lane 3 (3*s.val+t.val)=1 → s.val=0 := by decide
        exact tab ⟨a,al⟩ ⟨b,bl⟩ v.symm
      · have v := plateau_bit yes ⟨a,al⟩ ⟨b,bl⟩
        rw [hm] at v; by_contra! h; simp [h] at v
    unfold NorthFanLines.mark; omega
  apply right_bits q j i a b al bl (by omega) (by omega)
  have read : (marked F (L7.view w (35+42*u:Nat) (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat =
      lane (history q j i) (3*a+b) := by
    apply ShortBirth.mark_read _ _ al bl
    · by_cases early : j≤1
      · exact ShortBirth.birth_tile S acy (by omega) (by omega) early (by omega) (by omega)
      rw [row (by omega) (by omega) (by omega) (by omega),LiveCut.eastern (by omega) (by omega) (by omega)]
      unfold edge LiveCut.mword; split_ifs <;> rfl
    · by_cases z : j=0
      · subst j; simp only [history,if_true]; unfold seedWord; split_ifs <;> decide
      rw [LiveCut.eastern (by omega) (by omega) (by omega)]; unfold LiveCut.mword; split_ifs <;> decide
  rw [hm] at read; exact read.symm

def fits (k q : Nat) : Prop :=
  let y := q/6
  let f := q+2-3*y-8+6
  53≤k ∧ 35≤q ∧ q+6≤k ∧ 4≤y ∧ 6*y+3≤q ∧
    (Guarded.endFits k (k-(y+1)) f → 6*y+4≤q) ∧ Guarded.atCut k q (y+1) f
instance (k q) : Decidable (fits k q) := by unfold fits Guarded.endFits; infer_instance

theorem exclude {u F P w q} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : fits (11+14*u) q) : False := by
  let y := q/6; let x := q+2-3*y-8
  obtain ⟨hk,big,room,yl,fan,wide,ck⟩ := ok
  have off : q+2=x+8+3*y := by dsimp [x,y]; omega
  obtain ⟨fr,pl⟩ := front S H acy one score hk big room yl fan off
  exact Guarded.exclude_from_cut H acy one score hk S.room (y:=y+1) (f:=x+6) ck
    (by omega) (by dsimp [y] at *; omega) (by push_cast; omega) fr (fun h => pl (wide h))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.WideExitCut
