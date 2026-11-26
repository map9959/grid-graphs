import GridGraphs.ResidueTwoUpper.OneGap.RootCoverEmpty
import GridGraphs.ResidueTwoUpper.OneGap.CrampedIndices
import GridGraphs.ResidueTwoUpper.OneGap.FanSouthCollision
import GridGraphs.ResidueTwoUpper.OneGap.CollisionBand
import GridGraphs.ResidueTwoUpper.OneGap.OffBandMove
import GridGraphs.ResidueTwoUpper.OneGap.DanglingBandStep
import GridGraphs.ResidueTwoUpper.OneGap.CornerDrift
import GridGraphs.ResidueTwoUpper.OneGap.LargeScoredRoute
import GridGraphs.ResidueTwoUpper.OneGap.RowSevenBuffer
import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryExit
import GridGraphs.ResidueTwoUpper.OneGap.GuardedSchedules
import GridGraphs.ResidueTwoUpper.OneGap.LiveFanCut
import GridGraphs.ResidueTwoUpper.OneGap.ShortBirthCut
import GridGraphs.ResidueTwoUpper.OneGap.WideExitCut
import GridGraphs.ResidueTwoUpper.OneGap.MaskedCut49
import GridGraphs.ResidueTwoUpper.OneGap.MaskedCut51
import GridGraphs.ResidueTwoUpper.OneGap.DeepLiveCut
import GridGraphs.ResidueTwoUpper.OneGap.LastLongCut

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero L7 FanSeed FanSlab FanBoot Camera Port BoundarySix.Connected FanBoot.SouthCap

def RootFailure {u} (F : Finset (Site u)) (w : View) (q : Nat) : Prop :=
  let k := 11+14*u
  let f := max 3 (q+1)+12
  ∃ j<(k-21)/4,
    Front F w q k (4+4*j) (f+3*j) ∧ ¬Straight F w (4+4*j) (f+3*j) 9 9 ∧
    (∀ i<j, Straight F w (4+4*i) (f+3*i) 9 9)

def LongFailure {u} (F : Finset (Site u)) (w : View) (q : Nat) : Prop :=
  let k := 11+14*u
  let Y := (q-15)/6
  Front F w q k (Y+2) (q-3*Y+3) ∧
    k+15*Y+12<4*(q+1) ∧
    Plateau F w (Y+2) (Y+6) (q-3*Y+2) k ∧
    ((u,q)∈Speed.longPending ∧ ¬bridgeRoom k q ∧ Guarded.fits k q=false ∧ LiveCut.fits k q=false ∧
      DeepCut.fits k q=false ∧ (u,q)≠(4,65)) ∧
    ((u<12 ∧ (u<6 ∨ q∈Speed.earlyExceptions u)) ∨
     OffBandMove F w q (Y+6))

private theorem long_failure_of_seed {u : Nat} {F : Finset (Site u)} {P w q}
    (S : Short.Seed F P w q) (rim' : ∃ s f, rim F w s f)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (H : PhysicalHalo u F w q (fanDirection u w))
    (noSouth : ¬SouthEnd F w q) (big : 57≤q) :
    LongFailure F w q := by
  classical
  obtain ⟨s,f,side⟩ := rim'
  let Y := (q-15)/6
  have zs := S.zero
  have fit := S.room
  obtain ⟨front,row₀,row₁⟩ := front_rows_from_seed north_output u q big S.room S.odd F acy w s f side
    P S.step S.clean (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using zs)
    S.west (by rw [tile_eq F w (by omega)]; exact S.paid)
    (fun i lo hi => by rw [tile_eq F w (by omega)]; exact S.east i lo hi)
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  obtain ⟨extended,past⟩ := CollisionWide.plateau_with_guard H acy one score S big Y rfl Q row₀ row₁ front
  have rb := CollisionWide.reach_bounds (q-6*Y)
  have rect : Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) :=
    fun j lo hi => extended j lo (by omega)
  have narrow : 11+14*u+15*Y+12<4*(q+1) := by
    by_contra! wide
    have next := advance_front F w (by omega) le_rfl (by omega)
      (fun t st rt => by push_cast at *; omega) front rect
    have mid := CornerCone.blocks H acy one score (by omega) (y:=Y+6) (a:=q-3*Y+2)
      (f:=q+1) (s:=Y-1) (by omega) (by dsimp [Y]; omega) (by dsimp [Y]; omega)
      (by dsimp [Y] at *; omega) (by dsimp [Y]; omega) (by omega) (rect _ (by omega) le_rfl)
      (fun i l h => next.2.2 i (by omega) h (by omega))
    have out := CornerCone.cone H acy one score (by omega) (D:=2)
      (by omega) (by dsimp [Y]; omega) (by dsimp [Y]; omega)
      (by dsimp [Y] at *; omega) (by dsimp [Y]; omega) mid.1 mid.2 (by omega) 2 le_rfl
    apply FanBoot.SouthCap.Strip.GridScan.Rooted.Mixed.exclude_suffix H acy one score (by omega)
      (Y+6+4*(Y-1)+2) (q+1) (by omega) (by omega) (by dsimp [Y]; omega)
      (by dsimp [Y] at *; omega) (by dsimp [Y] at *; omega)
    exact fun i l h => ⟨.inl (out.1 i (by dsimp [Y] at *; omega) h),out.2 i l h⟩
  have pending := (Speed.pending_or_route big S.room S.odd narrow).resolve_right
    (fun route => noSouth (roomy_south_end H acy one score (by omega) big S.room route front rect))
  refine ⟨front,narrow,rect,⟨pending,fun ok => exclude_bridge H acy one score S.room ok front rect,
    Bool.eq_false_iff.mpr (fun ok => Guarded.exclude H acy one score big S.room ok front extended),
    Bool.eq_false_iff.mpr (fun ok => LiveCut.exclude S H acy one score big ok front),
    Bool.eq_false_iff.mpr (fun ok => DeepCut.exclude S H acy one score big ok front),?_⟩,?_⟩
  · intro eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact LastLong.exclude S H acy one score front
  by_cases sched : 12≤u ∨ (6≤u ∧ q∉Speed.earlyExceptions u)
  · right
    apply off_band_of_score H acy one score (by omega) (by omega) S.room
    by_contra free
    exact noSouth (to_south_end_unblocked u q big S.room F acy w P S.step S.clean
      (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using zs) Q
      ((Speed.schedule_iff u q big S.room S.odd).mpr sched) front rect (fun _ => past) free)
  · left; push Not at sched
    exact ⟨sched.1,(lt_or_ge u 6).imp id sched.2⟩

/-- The spaced-root branch is gone. A remaining short index is
confined to the small sides; long indices must also escape the
rooted suffix at their actual first collision. -/
def FanFailure {u} (F : Finset (Site u)) (w : View) (q : Nat) : Prop :=
  (11+14*u+3<4*(max 3 (q+1)+12) ∧ ¬(Short.North.Deep.bufferedRoom u q ∨
    Short.North.Deep.sixBuffer u q ∨ Short.North.Deep.sevenBuffer u q ∨
    EastBoundary.capRoom u q ∨ EastBoundary.exitRoom u q ∨ ShortBirth.fits (11+14*u) q ∨
    WideExitCut.fits (11+14*u) q ∨ (u,q)=(3,49) ∨ (u,q)=(3,51))) ∧
    (if q<57 then (u,q)∈Short.Cramped.pending else LongFailure F w q)

def pendingFanIndices := (Short.Cramped.pending ++
    Speed.longPending.filter (fun p => !decide (bridgeRoom (11+14*p.1) p.2) &&
      !Guarded.fits (11+14*p.1) p.2 && !LiveCut.fits (11+14*p.1) p.2 && !DeepCut.fits (11+14*p.1) p.2 &&
      decide (p≠(4,65)))).filter
  fun p => !decide (Short.North.Deep.bufferedRoom p.1 p.2 ∨ Short.North.Deep.sixBuffer p.1 p.2 ∨
    Short.North.Deep.sevenBuffer p.1 p.2 ∨ EastBoundary.capRoom p.1 p.2 ∨ EastBoundary.exitRoom p.1 p.2 ∨
    ShortBirth.fits (11+14*p.1) p.2 ∨ WideExitCut.fits (11+14*p.1) p.2 ∨ p=(3,49) ∨ p=(3,51))

theorem pendingFanIndices_empty : pendingFanIndices=[] := by native_decide

theorem pendingFanIndices_checked : pendingFanIndices.length=0 ∧ pendingFanIndices.Nodup ∧
    pendingFanIndices.all (fun p => decide (p.1=3)) := by native_decide

/-- Diagnose the long residual before looking for stronger window
admission lemmas. Count the indices where unrestricted eight-size
displacements fail from every certified collision row. -/
theorem pending_capacity_checked :
    (pendingFanIndices.filter (fun p => decide (57≤p.2))).length=0 ∧
    (pendingFanIndices.filter (fun (u,q) =>
      decide (57≤q) && !Guarded.hasCapacity (11+14*u) q)).length=0 := by native_decide

theorem fanFailure_index {u F w q} (h : FanFailure (u:=u) F w q) : (u,q)∈pendingFanIndices := by
  have fail := h.2
  apply List.mem_filter.mpr
  refine ⟨?_,?_⟩
  swap
  · simp only [Bool.not_eq_true',decide_eq_false_iff_not]
    exact h.1.2
  apply List.mem_append.mpr
  split at fail
  · exact .inl fail
  · obtain ⟨mem,no,miss,live,deep,last⟩ := fail.2.2.2.1
    exact .inr (List.mem_filter.mpr ⟨mem,by simp [no,miss,live,deep,last]⟩)

/-- In the long branch, passing the relaxed displacement test now
rules out failure. The physical implication uses `fanFailure_index`;
this is not a completeness claim for schedules on arbitrary states. -/
theorem no_long_failure_of_capacity {u F w q} (big : 57≤q)
    (cap : Guarded.hasCapacity (11+14*u) q) : ¬FanFailure (u:=u) F w q := by
  intro fail
  have all : pendingFanIndices.all (fun (a,b) =>
      decide (b<57) || !Guarded.hasCapacity (11+14*a) b) := by native_decide
  have hit := List.all_eq_true.mp all _ (fanFailure_index fail)
  change (decide (q<57) || !Guarded.hasCapacity (11+14*u) q)=true at hit
  simp [cap,show ¬q<57 by omega] at hit

theorem no_fan_failure_large {u F w q} (large : 4≤u) : ¬FanFailure (u:=u) F w q := by
  intro h
  have bound := of_decide_eq_true (List.all_eq_true.mp pendingFanIndices_checked.2.2 _ (fanFailure_index h))
  change u=3 at bound
  omega

/-- The new cut applies to an unbounded strip of long indices, independent
of the speed schedule or any hypothesis that movement windows are straight. -/
theorem no_fan_failure_of_buffer {u F w q} (long : 57≤q)
    (room : let Y := (q-15)/6; 4*(q+1)≤11+14*u+15*Y+12) :
    ¬FanFailure (u:=u) F w q := by
  rintro ⟨_,fail⟩
  rw [if_neg (by omega : ¬q<57)] at fail
  exact (Nat.not_le_of_gt fail.2.1) room

theorem failure_with_halo_from_score {u : Nat} {F : Finset (Site u)} (hu : 3≤u)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    ∃ P w q, Short.Seed F P w q ∧ Nonempty (PhysicalHalo u F w q (fanDirection u w)) ∧ FanFailure F w q := by
  obtain ⟨P,w,q,S,side,⟨H⟩⟩ := seeded_halo acy score one
  have cramped : 11+14*u+3<4*(max 3 (q+1)+12) := by
    by_cases small : u=3
    · omega
    by_contra! space
    exact roomy_impossible S H acy one score space (by omega)
  refine ⟨P,w,q,S,⟨H⟩,⟨cramped,fun ok => ok.elim (Short.North.Deep.exclude_buffered S H acy one score)
    (fun h => h.elim (Short.North.Deep.exclude_sixBuffer S H acy one score)
      (fun e => e.elim (Short.North.Deep.exclude_sevenBuffer S H acy one score)
        (fun z => z.elim (EastBoundary.exclude_room S H acy one score)
          (fun a => a.elim (EastBoundary.exclude_exit S H acy one score)
            (fun b => b.elim (ShortBirth.exclude S H acy one score)
               (fun c => c.elim (WideExitCut.exclude S H acy one score) ?_))))))⟩,?_⟩
  · rintro (eq|eq)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      exact NorthCut161.exclude49 S H acy one score
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      exact NorthCut161.exclude51 S H acy one score
  split
  · rename_i short
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ?_,?_⟩
    swap
    · simp only [Bool.not_eq_true',decide_eq_false_iff_not]
      exact fun h => h.elim (Short.Cramped.exclude_sevenRoom S H acy one score)
        (fun rest => rest.elim (Short.Cramped.exclude_eightRoom S H acy one score)
          (Short.Cramped.exclude_nineRoom S H acy one score))
    refine ⟨Short.Cramped.mem_indices.mpr (decide_eq_true ⟨hu,by omega,S.odd,short,S.room,cramped⟩),?_⟩
    simp only [Bool.not_eq_true',Bool.or_eq_false_iff,decide_eq_false_iff_not]
    exact ⟨⟨Bool.eq_false_iff.mpr (fun hit => Short.Cramped.exclude_passed
      (List.contains_iff_mem.mp hit) S H acy one score), Short.Cramped.exclude_translated S H acy one score⟩,
      Short.Cramped.exclude_deeper S H acy one score⟩
  · have room := S.room
    exact long_failure_of_seed S side acy score one H
      (no_south_of_room H acy one score (by omega) room) (by omega)

theorem failure_from_score {u : Nat} {F : Finset (Site u)} (hu : 3≤u)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    ∃ P w q, Short.Seed F P w q ∧ FanFailure F w q := by
  obtain ⟨P,w,q,S,_,bad⟩ := failure_with_halo_from_score hu acy score one
  exact ⟨P,w,q,S,bad⟩

/-- Beyond side 791 a putative score forces a long-index obstruction;
no short-fan theorem or sparse-location hypothesis is an input. -/
theorem score_forces_long {u : Nat} {F : Finset (Site u)} (hu : 19≤u)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    ∃ P w q, Short.Seed F P w q ∧ 57≤q ∧ LongFailure F w q := by
  obtain ⟨P,w,q,S,_,fail⟩ := failure_from_score (by omega) acy score one
  by_cases short : q<57
  · rw [if_pos short] at fail
    have fit := Short.Cramped.mem_indices.mp (List.mem_filter.mp (List.mem_filter.mp fail).1).1
    simp only [Short.Cramped.fits,decide_eq_true_eq] at fit
    omega
  · exact ⟨P,w,q,S,by omega,by rwa [if_neg short] at fail⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
