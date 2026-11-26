import GridGraphs.ResidueTwoUpper.OneGap.DepthEightCheck
import GridGraphs.ResidueTwoUpper.OneGap.DepthSevenTransfer

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

theorem eight_sites {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (left : 25≤q) (room : q+17≤11+14*u) (j : Nat) (jl : 2≤j) (jh : j≤8) :
    ∃ b, 2≤b ∧ b≤q+1 ∧ square F w (1+3*j) (1+3*b)=73 := by
  have witness : ∃ d b, 18≤d ∧ d≤22 ∧ b≤d+1 ∧
      bigFixed (profileGrid (cached 3 chart) w 6 d) w j b := by
    by_cases old : j≤7
    · obtain ⟨b,bh,m⟩ := seven_interior w jl old
      exact ⟨18,b,le_rfl,by decide,by omega,m⟩
    · obtain ⟨d,b,ds,bh,m⟩ := eight_new_row w
      exact ⟨d,b,by omega,by omega,bh,by rwa [show j=8 by omega]⟩
  obtain ⟨d,b,dl,dh,bh,m⟩ := witness
  let v := q-d
  have eq : v+d=q := by dsimp [v]; omega
  exact ⟨v+b,by omega,by omega,read_big (s:=6) (eq ▸ S : Seed F P w (v+d)) acy
    (.inr ⟨by omega,by decide⟩) (by decide) (by omega) (by omega) (by omega) m⟩

theorem eight_suffix {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (hk : 53≤11+14*u) (left : 25≤q) (room : q+17≤11+14*u) :
    ∀ i, q+1 ≤ i → i<11+14*u → tile F w 8 i=73 ∧ RootLine F w i 8 :=
  suffix_from_sites S acy (by decide) (eight_sites S acy left room) hk (by omega) room

theorem exclude_eight {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (left : 25≤q) (room : q+17≤11+14*u)
    (width : 4*(q+1)≤11+14*u+24) : False := by
  apply Mixed.exclude_suffix H acy one score hk 8 (q+1) (by decide) (by omega)
    (by omega) (by omega) (by omega)
  intro i il ih
  obtain ⟨m,line⟩ := eight_suffix S acy hk left room i il ih
  exact ⟨.inl m,line⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
