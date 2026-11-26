import GridGraphs.ResidueTwoUpper.OneGap.DepthNineCheck
import GridGraphs.ResidueTwoUpper.OneGap.DepthEightTransfer

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

theorem nine_suffix {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (hk : 53≤11+14*u) (place : q=19 ∨ 29≤q) (room : q+17≤11+14*u) :
    ∀ i, q+1 ≤ i → i<11+14*u → tile F w 9 i=73 ∧ RootLine F w i 9 := by
  apply suffix_from_sites S acy (by decide) _ hk (by omega) room
  intro j jl jh
  rcases place with rfl|lo
  · obtain ⟨b,bl,bh,m⟩ := nine_wall w jl jh
    refine ⟨b,bl,bh,?_⟩
    simpa only [Nat.zero_add] using read_big (v:=0) (s:=0) (d:=19)
      S acy (.inl ⟨rfl,rfl⟩) (by decide) (by omega) (by omega) (by omega) m
  · by_cases old : j≤8
    · exact eight_sites S acy (by omega) room j jl old
    · obtain ⟨d,b,dl,dh,bh,m⟩ := nine_interior w
      let v := q-d
      have eq : v+d=q := by dsimp [v]; omega
      refine ⟨v+b,by omega,by omega,?_⟩
      rw [show j=9 by omega]
      exact read_crop 32 (s:=6) (eq ▸ S : Seed F P w (v+d)) acy (.inr ⟨by omega,by decide⟩)
        (by decide) (by omega) (by decide) (by omega) m

theorem exclude_nine {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (place : q=19 ∨ 29≤q) (room : q+17≤11+14*u)
    (width : 4*(q+1)≤11+14*u+27) : False := by
  apply Mixed.exclude_suffix H acy one score hk 9 (q+1) (by decide) (by omega)
    (by omega) (by omega) (by omega)
  intro i il ih
  obtain ⟨m,line⟩ := nine_suffix S acy hk place room i il ih
  exact ⟨.inl m,line⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
