import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay
import GridGraphs.ResidueTwoUpper.OneGap.CornerDrift

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- Keep the physical catalogue on all thirteen columns. Only ten
columns of the top edge are required to have the plain mask. -/
private def trimBank : Bank := fun r c =>
  (bankWords (endTag 14 r) (endTag (width 14) c)).filter fun w =>
    decide (r=0 → (3≤c → w.1=73) ∧ (3≤c+1 → w.2.1=73))
private def rail (m : Nat) := bit m 1==1 || bit m 3==1
private theorem trim_checked : (List.range 13).all fun r =>
    (matrixRead (seams 14 (matrixOf 14 trimBank) 26) r 11).all fun w =>
      rail w.2.1 && bit w.2.2.2 0==1 && rail w.2.2.2 := by native_decide

private theorem trim14 {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-14))
    (top : ∀ i, 11+14*u-10 ≤ i → i<11+14*u →
      Rooted.tile F v (11+14*u-14) i=73) : False := by
  let k := 11+14*u
  let t := cropTiles F v k 14
  let m := seams 14 (matrixOf 14 trimBank) 26
  have w : width 14=13 := rfl
  have fit : FitsTiles t := physical_tiles_fit F v _ _
  have bank : OrdinaryCapAdmitted F v k 14 := by
    intro r c hr hc
    exact physical_rectangle_word ⟨rfl,hk,by dsimp [k]; omega,by rw [w]; dsimp [k]; omega,hr,hc⟩ H acy score
  have ok : MatrixAdmits 14 m t := by
    apply seams_sound
    intro r c hr hc
    change word t r c ∈ matrixRead (matrixOf 14 trimBank) r c
    rw [matrixRead_of _ _ _ _ hr hc]
    apply List.mem_filter.mpr
    have adm := bank r c hr hc
    refine ⟨bankWords_cover ⟨fit r c,fit r (c+1),fit (r+1) c,fit (r+1) (c+1)⟩
      (by simpa [t,word,cropTiles,Nat.mul_add,Nat.add_assoc,k] using adm),?_⟩
    apply decide_eq_true
    rintro rfl
    have read (j : Nat) (l : 3≤j) (hi : j<width 14) : t 0 j=73 := by
      have z := top (k-width 14+j) (by dsimp [k]; omega) (by dsimp [k]; omega)
      simpa [t,cropTiles,firstCol,firstRow,Rooted.tile,k,Nat.mul_add,Nat.add_assoc] using z
    exact ⟨fun l => read c l (by omega),fun l => read (c+1) l (by omega)⟩
  let T := fun j => Rooted.tile F v (k-14+j) (10+14*u)
  have idx (j : Nat) : t j 12=T j := by
    unfold t T cropTiles Rooted.tile firstRow firstCol
    rw [w]; congr 1 <;> dsimp [k] <;> omega
  have info (j : Nat) (hj : j<13) :
      ((bit (T j) 1=1 ∨ bit (T j) 3=1) ∧ bit (T (j+1)) 0=1) ∧
      (bit (T (j+1)) 1=1 ∨ bit (T (j+1)) 3=1) := by
    have ck := List.all_eq_true.mp (List.all_eq_true.mp trim_checked j (List.mem_range.mpr hj))
      _ (ok j 11 (by omega) (by decide))
    change ((rail (t j 12) && bit (t (j+1) 12) 0==1) && rail (t (j+1) 12))=true at ck
    simpa only [rail,idx,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using ck
  have roots (j : Nat) (hj : j≤13) : RootLine F v (10+14*u) (k-14+j) := by
    induction j with
    | zero => simpa only [k,Nat.add_zero,show 11+14*u-1=10+14*u by omega] using line
    | succ j ih =>
      have old := ih (by omega)
      have data := info j (by omega)
      apply Rooted.extend_line old
      · exact data.1.1.resolve_left (Rooted.no_east_middle H acy one (by dsimp [k]; omega) (by dsimp [k]; omega) old)
      · exact .inr data.1.2
  have last := roots 13 le_rfl
  have ends := (info 12 (by decide)).2
  change bit (Rooted.tile F v (k-14+13) _) 1=1 ∨ bit (Rooted.tile F v (k-14+13) _) 3=1 at ends
  rw [show k-14+13=10+14*u by dsimp [k]; omega] at ends last
  exact ends.elim (Rooted.no_east_middle H acy one (by omega) (by omega) last)
    (Rooted.no_south_middle H acy one (by omega) (by omega) last)

def topWidth (h : Nat) := let d := h-14; 3*(d/4)+d%4+10

theorem topWidth_saving {h : Nat} (lo : 14≤h) :
    topWidth h+2≤width h ∧ width h≤topWidth h+3 := by
  dsimp [topWidth,width]
  omega

/-- Uniform in height. Carry a single eastern root and the plain row
down to the trimmed base cap, at three columns per four rows. -/
theorem trimmed_excludes_of_ge53 {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a : Nat} (yl : 4≤y) (al : 5≤a) (ht : y+14≤11+14*u)
    (space : a+topWidth (11+14*u-y)≤11+14*u)
    (top : ∀ i, a ≤ i → i<11+14*u → Rooted.tile F v y i=73)
    (line : RootLine F v (11+14*u-1) y) : False := by
  let k := 11+14*u; let d := k-y-14
  change a+(3*(d/4)+d%4+10)≤k at space
  have mid := CornerCone.blocks H acy one score (by omega) (s:=d/4) (f:=k-1) yl al
    (by dsimp [k,d]; omega) (by dsimp [k] at *; omega) (by omega) (by dsimp [k]; omega)
    top (fun i l hi => by rwa [show i=k-1 by dsimp [k] at *; omega])
  have tail := CornerCone.cone H acy one score (by omega) (D:=d%4)
    (by omega) (by omega) (by dsimp [k,d]; omega) (by dsimp [k] at *; omega)
    (by omega) mid.1 mid.2 (by dsimp [k]; omega) (d%4) le_rfl
  rw [show y+4*(d/4)+d%4=k-14 by dsimp [d,k]; omega] at tail
  exact trim14 H acy one score hk (tail.2 _ le_rfl (by omega))
    (fun i l hi => tail.1 i (by dsimp [k] at *; omega) hi)

theorem trimmed_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    {y a : Nat} (yl : 4≤y) (al : 5≤a) (ht : y+14≤11+14*u)
    (space : a+topWidth (11+14*u-y)≤11+14*u)
    (top : ∀ i, a ≤ i → i<11+14*u → Rooted.tile F v y i=73)
    (line : RootLine F v (11+14*u-1) y) : False :=
  trimmed_excludes_of_ge53 H acy one score (by omega) yl al ht space top line
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
