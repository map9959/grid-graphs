import GridGraphs.ResidueTwoUpper.OneGap.RootCoverWave
import GridGraphs.ResidueTwoUpper.OneGap.RootCorridorPacking

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero L7 FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan

theorem no_wide_front {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    {y f a : Nat} (front : Front F w q (11+14*u) y a)
    (inside : a≤f) (feet : q<f) (yl : 4≤y) (fl : 4≤f)
    (height : y+8≤11+14*u) (width : f+8≤11+14*u)
    (slope : 3*(11+14*u-y)+8≤4*(11+14*u-f)) : False := by
  have words := Rooted.physical_label_bank H acy one score (by omega) y f yl fl (by omega)
    (fun i il ir => ⟨front.1 _ le_rfl le_rfl _ (by omega) ir,front.2.2 i (by omega) ir (by omega)⟩)
  exact Rooted.Wave.no_field _ _ (by omega) (by omega) slope _ words

/-- The actual scored constraints cover every potential bad location
on every spaced route by the empty set: the incoming front of such a
window would itself extend over a rectangle forbidden by `no_field`. -/
theorem empty_route_cover {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (space : 4*(max 3 (q+1)+12)≤11+14*u+3) (hk : 59≤11+14*u) :
    ∀ i : Fin (corridorCount u q), ∀ p,
      BadAt F w q (max 3 (q+1)+12+16*i.val) p → p∈(∅ : Finset (Nat × Nat)) := by
  intro i p bad
  obtain ⟨j,jl,front,_⟩ := bad
  have il := i.isLt
  unfold corridorCount at il
  let f := max 3 (q+1)+12+16*i.val+3*j
  have budget : 4*(max 3 (q+1)+12+16*i.val)≤11+14*u+3 := by omega
  exact (no_wide_front H acy one score hk (f:=f) front le_rfl
    (by dsimp [f]; omega) (by omega) (by dsimp [f]; omega)
    (by omega) (by dsimp [f]; omega) (by dsimp [f]; omega)).elim

theorem roomy_impossible {u F w q P} (S : Short.Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (space : 4*(max 3 (q+1)+12)≤11+14*u+3) (hk : 59≤11+14*u) : False :=
  no_south_of_room H acy one score hk S.room
    (south_of_sparse_failures S acy score one space hk ∅
      (by simp [corridorCount]) (empty_route_cover H acy one score space hk))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
