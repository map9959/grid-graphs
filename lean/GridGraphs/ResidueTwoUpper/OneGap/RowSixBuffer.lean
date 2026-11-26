import GridGraphs.ResidueTwoUpper.OneGap.ShortBufferedFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero L7 FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

@[noinline] private def sixth (A : Board) :=
  decide (∀ w : View, wideFixed 138 (wideGrid A w 138 3 39) w 6 23)
private theorem sixth_checked : sixth (cached 3 chart) := by native_decide

def sixBuffer (u q : Nat) : Prop :=
  53≤11+14*u ∧ 42≤q ∧ q+17≤11+14*u ∧ 4*(q+1)≤11+14*u+84
instance (u q) : Decidable (sixBuffer u q) := by unfold sixBuffer; infer_instance

theorem exclude_sixBuffer {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : sixBuffer u q) : False := by
  obtain ⟨hk,left,room,slope⟩ := ok
  let v := q-39
  have eq : v+39=q := by dsimp [v]; omega
  have tooth := read_crop 46 (s:=3) (d:=39) (j:=6) (i:=23) (eq ▸ S : Seed F P w (v+39)) acy
    (.inr ⟨by dsimp [v]; omega,by decide⟩) (by decide) (by omega) (by decide) (by decide)
    (of_decide_eq_true sixth_checked w)
  have fr := from_buffer S H acy one score hk (by omega) room (r:=6) (a:=v+23) (s:=5)
    (by decide) (by omega) (by omega) (by omega) tooth
  apply Mixed.exclude_suffix H acy one score hk 28 (q+1) (by decide) (by omega)
    (by omega) (by omega) (by omega)
  exact fun i lo hi => ⟨.inl (fr.1 _ le_rfl le_rfl i lo hi),fr.2.2 i lo hi (by omega)⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
