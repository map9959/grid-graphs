import GridGraphs.ResidueTwoUpper.OneGap.DepthSevenCheck
import GridGraphs.ResidueTwoUpper.OneGap.DepthSixTransfer

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap

/-- Transfer row-seven witnesses from either an interior chart or the
actual west wall, and grow a rooted suffix from column `q+1`. -/
theorem exclude_seven {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (placement : q=17 ∨ 21≤q) (room : q+17≤11+14*u)
    (width : 4*(q+1)≤11+14*u+21) : False := by
  apply exclude_with_sites S H acy one score (y:=7) (e:=1) (by decide) _ hk (by omega) room width
  intro j jl jh
  rcases placement with rfl|lo
  · obtain ⟨b,bl,bh,ok⟩ := seven_wall w jl jh
    exact ⟨b,bl,bh,by
      simpa only [Nat.zero_add] using read_big (s:=0) (v:=0) (d:=17) S acy (.inl ⟨rfl,rfl⟩)
        (by decide) (by omega) (by omega) (by omega) ok⟩
  · let v := q-18
    have eq : v+18=q := by dsimp [v]; omega
    obtain ⟨b,hb,ok⟩ := seven_interior w jl jh
    exact ⟨v+b,by omega,by omega,read_big (s:=6) (eq ▸ S : Seed F P w (v+18)) acy
      (.inr ⟨by omega,by decide⟩) (by decide) (by omega) (by omega) (by omega) ok⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
