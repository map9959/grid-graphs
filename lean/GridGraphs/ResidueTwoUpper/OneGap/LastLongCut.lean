import GridGraphs.ResidueTwoUpper.OneGap.DeepLiveCut
import GridGraphs.ResidueTwoUpper.OneGap.DepartureRim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.LastLong
open ResidueZero Stencil L7 FanSlab FanSeed Short FanSweep EastBoundary BoundarySix.Connected SouthCap

private def localGrid := build ⟨24,84,[]⟩ fun r c =>
  ((priceTable[5+(r+1)%3]!)[(c+1)%3]!).filter fun m =>
    r%3 != 0 || r>3 || c%3 != 0 || m==transpose (actual 65 (8+r/3) (20+c/3))
private def output (g : Grid) :=
  (cell g 9 36).all (·==2) && (cell g 9 39).all (fun m => m==8 || m==72) &&
  (cell g 9 42).all (fun m => m==9 || m==73) &&
  (List.range 3).all fun j => (cell g 6 (3*(14+j))).all (·==transpose (actual 65 10 (34+j)))
private theorem checked : output (EastBoundary.Kernel.prune 25 85 100 localGrid) := by native_decide

/-- Local physical read at the meeting of the two fan boundaries. The
two input rows are the actual long-seed history, not an assumed row 10. -/
private theorem collision {u F w P} (S : Seed (u:=u) F P w 65) (acy : (Bonds F).IsAcyclic)
    (R : ∀ j≤9, Read (35+42*u) 65 j F w) :
    maskAtTile F w 11 32=2 ∧ (maskAtTile F w 11 33=8 ∨ maskAtTile F w 11 33=72) ∧
    (maskAtTile F w 11 34=9 ∨ maskAtTile F w 11 34=73) ∧
    ∀ i, 34 ≤ i → i<37 → maskAtTile F w 10 i=transpose (actual 65 10 i) := by
  let M := fun r c => square F w (25+r) (61+c)
  have room := S.room
  have init (r : Nat) (hr : r<25) (c : Nat) (hc : c<85) : M r c∈EastBoundary.Kernel.get localGrid r c := by
    have reg := accept_bulk u (24+r) (60+c) (by omega) (by omega) F acy P S.step w S.clean (by
      intro v loc; apply S.zero; rw [loc]; intro eq
      cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at eq <;> omega)
    rw [show rowTag (24+r)=5+(r+1)%3 by unfold rowTag; split <;> omega,
      show realTag u (60+c)=5+(c+1)%3 by unfold realTag; split_ifs <;> omega] at reg
    have valid : accepts (5+(r+1)%3) (5+(c+1)%3) (M r c) := by
      simpa only [M,show 1+(24+r)=25+r by omega,show 1+(60+c)=61+c by omega] using reg
    have pin : r%3 != 0 || r>3 || c%3 != 0 || M r c==transpose (actual 65 (8+r/3) (20+c/3)) := by
      simp only [Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq,beq_iff_eq]
      by_contra! neg
      obtain ⟨⟨⟨rr,rh⟩,cc⟩,miss⟩ := neg
      apply miss
      have eq : M r c=maskAtTile F w (8+r/3) (20+c/3) := congrArg₂ (square F w) (by omega) (by omega)
      rw [eq]; apply align
      · have bd : ∀ j : Fin 2, ∀ i : Fin 29, actual 65 (8+j.val) (20+i.val)<512 := by decide
        exact bd ⟨_,by omega⟩ ⟨_,by omega⟩
      · intro a b
        simpa only [history,if_neg (by omega : 8+r/3≠0)] using
          R (8+r/3) (by omega) (20+c/3) a b (by have := a.isLt; omega) a.isLt b.isLt
    have bd : M r c<512 := (unpack _).1
    simpa [EastBoundary.Kernel.get,localGrid,FanSweep.build,priceTable,hr,hc,
      show 5+(r+1)%3<8 by omega,show (c+1)%3<3 by omega,bd,valid,pin]
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (25+r) (61+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (25+r) (61+c) false) 100 _ init
  have tab := checked
  simp only [output,Bool.and_eq_true] at tab
  refine ⟨beq_iff_eq.mp (List.all_eq_true.mp tab.1.1.1 _ (live 9 (by decide) 36 (by decide))),?_,?_,?_⟩
  · simpa only [Bool.or_eq_true,beq_iff_eq] using List.all_eq_true.mp tab.1.1.2 _ (live 9 (by decide) 39 (by decide))
  · simpa only [Bool.or_eq_true,beq_iff_eq] using List.all_eq_true.mp tab.1.2 _ (live 9 (by decide) 42 (by decide))
  · intro i il ih
    have test := List.all_eq_true.mp tab.2 (i-34) (List.mem_range.mpr (by omega))
    have hit := beq_iff_eq.mp (List.all_eq_true.mp test _ (live 6 (by decide) _ (by omega)))
    rw [show 34+(i-34)=i by omega] at hit
    exact (show M 6 (3*(14+(i-34)))=maskAtTile F w 10 i from congrArg₂ (square F w) rfl (by omega)) ▸ hit

theorem front {u F w P} (S : Seed (u:=u) F P w 65)
    (H : PhysicalHalo u F w 65 (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (old : Front F w 65 (11+14*u) 10 44) :
    Front F w 65 (11+14*u) 11 35 ∧ Plateau F w 11 11 34 (11+14*u) := by
  have room := S.room
  have R := north_rows north_output u 65 (by decide) room S.odd F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) S.west
    (by rw [tile_eq F w (by omega)]; exact S.paid)
    (fun i lo hi => by rw [tile_eq F w (by omega)]; exact S.east i lo hi)
  obtain ⟨_,pl⟩ := DeepCut.front S acy (by decide) old
  change Plateau F w 10 10 37 (11+14*u) at pl
  have line (i : Nat) (rt : 65 < i) (hi : i<11+14*u) : RootLine F w i 11 := by
    have tooth : Strip.GridScan.Rooted.tile F w 10 i=73 := pl 10 le_rfl le_rfl i (by omega) hi
    apply Strip.GridScan.Rooted.extend_line (old.2.2 i (by omega) hi rt)
    · rw [tooth]; decide
    · left; rw [tooth]; decide
  obtain ⟨two,choice,east,prior⟩ := collision S acy R
  have last := line (11+14*u-1) (by omega) (by omega)
  have s := choice.resolve_left (fun eight => Departure.no28 H acy one score (by omega)
    (r:=11) (x:=32) (by decide) (by decide) (by omega) (by omega) (.inl two) eight east last)
  have next := Departure.ray H acy score (by omega) (r:=11) (c:=33) (n:=72)
    (by decide) (by decide) (by omega) (.inr rfl) (.inl s) 34 (by decide) (by omega)
  change maskAtTile F w 11 34=72 ∨ maskAtTile F w 11 34=73 at next
  have tooth : maskAtTile F w 11 34=73 := by omega
  have plain (i : Nat) (il : 34 ≤ i) (ih : i<11+14*u) : maskAtTile F w 11 i=73 := by
    induction i,il using Nat.le_induction with
    | base => exact tooth
    | succ i lo h =>
      exact east_step u 65 11 i (by omega) (by omega) (by omega) F acy w P S.step S.clean
        (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) (h (by omega))
  have guard : Plateau F w 11 11 34 (11+14*u) := by
    intro r lo hi i il ih; rw [show r=11 by omega]; exact plain i il ih
  refine ⟨⟨fun r l h i il ih => guard r l h i (by omega) ih,?_,fun i _ hi rt => line i rt hi⟩,guard⟩
  intro t tl th rt
  apply dangling_of_marks _ 65 11 t (by omega) (by omega) (by omega) rt
  intro j jh i a b _ it ti bound al bl m
  by_cases final : j=11
  · subst j
    have v := plateau_bit (plain i (by omega) (by omega)) ⟨a,al⟩ ⟨b,bl⟩
    rw [m] at v
    have az : a=0 := by by_contra! h; simp [h] at v
    unfold NorthFanLines.mark; omega
  apply right_bits 65 j i a b al bl (by omega) (by omega)
  by_cases early : j≤9
  · have h := R j early i a b bound al bl; rw [m] at h; exact h.symm
  obtain rfl : j=10 := by omega
  by_cases inside : i<37
  · have h := ShortBirth.mark_read (prior i (by omega) inside)
      (by
        have lo : 34 ≤ i := by omega
        interval_cases i <;> decide) al bl
    rw [m] at h; exact h.symm
  · have h := plateau_bit (pl 10 le_rfl le_rfl i (by omega) (by omega)) ⟨a,al⟩ ⟨b,bl⟩
    rw [m] at h
    have az : a=0 := by by_contra! ne; simp [ne] at h
    rw [LiveCut.eastern (by decide) (by decide) (by omega)]
    have val : LiveCut.mword (65+2-3*10) i=7 := by unfold LiveCut.mword; split_ifs <;> omega
    rw [val,az]; interval_cases b <;> decide
theorem exclude {F w P} (S : Seed (u:=4) F P w 65)
    (H : PhysicalHalo 4 F w 65 (fanDirection 4 w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*4+588*4^2)
    (old : Front F w 65 67 10 44) : False := by
  obtain ⟨fr,pl⟩ := front S H acy one score old
  have ck : Guarded.atCut 67 65 11 35 := by native_decide
  exact Guarded.exclude_from H acy one score (by decide) S.room (y:=11) (f:=35)
    ck (by decide) (by decide) (by decide) fr pl
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.LastLong
