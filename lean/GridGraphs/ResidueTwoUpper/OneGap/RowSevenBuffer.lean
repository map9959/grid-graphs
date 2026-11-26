import GridGraphs.ResidueTwoUpper.OneGap.RowSixBuffer
import GridGraphs.ResidueTwoUpper.OneGap.TrimmedCap

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

@[noinline] private def seventh (A : Board) :=
  decide (∀ w : View, wideFixed 141 (wideGrid A w 141 3 44) w 7 25)
private theorem seventh_checked : seventh (cached 3 chart) := by native_decide

def sevenBuffer (u q : Nat) : Prop :=
  59≤11+14*u ∧ 47≤q ∧ q+17≤11+14*u ∧ q-19+Strip.GridScan.topWidth (11+14*u-7)≤11+14*u
instance (u q) : Decidable (sevenBuffer u q) := by unfold sevenBuffer; infer_instance

theorem exclude_sevenBuffer {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : sevenBuffer u q) : False := by
  obtain ⟨hk,left,room,slope⟩ := ok
  let v := q-44
  have eq : v+44=q := by dsimp [v]; omega
  have tooth := read_crop 47 (s:=3) (d:=44) (j:=7) (i:=25) (eq ▸ S : Seed F P w (v+44)) acy
    (.inr ⟨by dsimp [v]; omega,by decide⟩) (by decide) (by omega) (by decide) (by decide)
    (of_decide_eq_true seventh_checked w)
  have roots := suffix_from_sites S acy (y:=7) (e:=1) (by decide)
    (fun j lo hi => eight_sites S acy (by omega) room j lo (by omega)) (by omega) (by omega) room
  apply Strip.GridScan.trimmed_excludes H acy one score hk (y:=7) (a:=v+25)
    (by decide) (by omega) (by omega) (by rwa [show v+25=q-19 by omega]) _
    (roots _ (by omega) (by omega)).2
  intro i l hi
  induction i,l using Nat.le_induction with
  | base => exact tooth
  | succ i l ih =>
    apply east_step u q 7 i (by omega) (by omega) (by omega) F acy w P S.step S.clean
    · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero
    · exact ih (by omega)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
