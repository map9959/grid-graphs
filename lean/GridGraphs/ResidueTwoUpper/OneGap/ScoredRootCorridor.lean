import GridGraphs.ResidueTwoUpper.OneGap.ShortSouth
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastAll

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero L7 FanSeed FanSlab FanBoot Camera Port BoundarySix.Connected
open FanBoot.SouthCap FanBoot.SouthCap.Strip.GridScan

/-- The bound 57 on the isolate index is not a cap hypothesis. It was
previously used just to get room on the board. -/
theorem no_south_of_room {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u) (fit : q+2≤11+14*u) :
    ¬SouthEnd F v q := by
  rintro ⟨h,f,⟨lo,hi,room⟩,pl,_,roots⟩
  change f+3*h/4+3≤11+14*u at room
  obtain ⟨rounds,rejected⟩ := eastRange_empty h lo hi
  exact east_empty_excludes H acy one score hk lo hi (roots _ (by omega) (by omega) (by omega))
    (fun i st en => pl _ le_rfl le_rfl i (by unfold width at st; omega) en) rounds rejected

theorem seeded_halo {u : Nat} {F : Finset (Site u)} (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ P w q, Short.Seed F P w q ∧ (∃ s f, rim F w s f) ∧
      Nonempty (PhysicalHalo u F w q (fanDirection u w)) := by
  obtain ⟨P,w,q,S,⟨s,f,side⟩,d,iso,pos⟩ := Short.located_seed_from_score u F acy score one
  obtain ⟨H⟩ := physical_halo u F acy score one w s f side q P d iso pos S.step
    (fun x ne => S.zero x (fun e => ne (coord_injective (e.trans pos.symm)))) (fanDirection u w)
  exact ⟨P,w,q,S,⟨s,f,side⟩,⟨H⟩⟩

/-- A putative score yields both the seed and the excluded southern
end in the very same view. No independent choice of a halo is needed. -/
theorem seeded_no_south {u : Nat} {F : Finset (Site u)} (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1)
    (hk : 59≤11+14*u) :
    ∃ P w q, Short.Seed F P w q ∧ (∃ s f, rim F w s f) ∧ ¬SouthEnd F w q := by
  obtain ⟨P,w,q,S,side,⟨H⟩⟩ := seeded_halo acy score one
  exact ⟨P,w,q,S,side,no_south_of_room H acy one score hk S.room⟩

/-- If the rooted route fails, locate an actual bad window with its
incoming teeth still attached. Only windows on this diagonal can be
selected, as opposed to an arbitrary bad tile in the lower square. -/
theorem first_root_failure_at {u : Nat} {F : Finset (Site u)} {P w q} (S : Short.Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (noSouth : ¬SouthEnd F w q)
    (f : Nat) (past : max 3 (q+1)+12 ≤ f) (space : 4*f≤11+14*u+3) (hk : 59≤11+14*u) :
    let k := 11+14*u
    ∃ j<(k-21)/4,
      Front F w q k (4+4*j) (f+3*j) ∧ ¬Straight F w (4+4*j) (f+3*j) 9 9 ∧
      (∀ i<j, Straight F w (4+4*i) (f+3*i) 9 9) := by
  classical
  let k := 11+14*u
  let t := (k-21)/4
  let h := k-4-4*t
  have rem : 17≤h ∧ h≤20 ∧ 4+4*t+h=k := by dsimp [h,t,k]; omega
  have finalRoom : f+3*t+3*h/4+3≤k := by dsimp [k] at *; omega
  have fr := Short.North.front S acy (by omega)
  have start : Front F w q k 4 f :=
    ⟨fun r hr hr' i il ir => fr.1 r hr hr' i (by omega) ir,
     fun i il ir iq => fr.2.1 i (by omega) ir iq,
     fun i il ir iq => fr.2.2 i (by omega) ir iq⟩
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have go (j : Nat) (jl : j≤t) (good : ∀ i<j, Straight F w (4+4*i) (f+3*i) 9 9) :
      Front F w q k (4+4*j) (f+3*j) := by
    induction j with
    | zero => simpa using start
    | succ j ih =>
      have prev := ih (by omega) (fun i il => good i (by omega))
      have next := physical_root_step u q (4+4*j) (f+3*j) (f+3*j)
        (by omega) le_rfl (by dsimp [k] at *; omega)
        F acy w P S.step S.clean (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero)
        Q (good j (by omega)) prev
      simpa only [Nat.mul_succ,Nat.add_assoc,k] using next
  have bad : ∃ i, i<t ∧ ¬Straight F w (4+4*i) (f+3*i) 9 9 := by
    by_contra! allGood
    have last := go t le_rfl allGood
    exact noSouth ⟨h,f+3*t,⟨by change 14≤h; omega,by change h≤43; omega,finalRoom⟩,by
      rwa [show 11+14*u-h=4+4*t by dsimp [k] at *; omega]⟩
  let j := Nat.find bad
  have spec := Nat.find_spec bad
  have earlier (i : Nat) (il : i<j) : Straight F w (4+4*i) (f+3*i) 9 9 := by
    by_contra neg
    have le := Nat.find_min' bad (show i<t ∧ _ from ⟨by dsimp [j] at il; omega,neg⟩)
    exact (Nat.not_le_of_gt il) le
  exact ⟨j,spec.1,go j (by dsimp [j]; omega) earlier,spec.2,earlier⟩

theorem first_root_failure {u : Nat} {F : Finset (Site u)} {P w q} (S : Short.Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (noSouth : ¬SouthEnd F w q)
    (space : 4*(max 3 (q+1)+12)≤11+14*u+3) (hk : 59≤11+14*u) :
    let k := 11+14*u
    let f := max 3 (q+1)+12
    ∃ j<(k-21)/4,
      Front F w q k (4+4*j) (f+3*j) ∧ ¬Straight F w (4+4*j) (f+3*j) 9 9 ∧
      (∀ i<j, Straight F w (4+4*i) (f+3*i) 9 9) :=
  first_root_failure_at S acy score one noSouth _ le_rfl space hk

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
