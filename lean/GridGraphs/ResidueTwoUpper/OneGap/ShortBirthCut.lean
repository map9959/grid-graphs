import GridGraphs.ResidueTwoUpper.OneGap.LiveFanCut
import GridGraphs.ResidueTwoUpper.OneGap.NorthFirstStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.ShortBirth
open ResidueZero Stencil L7 FanSlab Short FanSweep EastBoundary LiveCut
open BoundarySix.Connected SouthCap

private def G := chart true 12 0 2 8
private theorem checked :
    let f := Kernel.prune 16 37 80 G
    (List.range 2).all fun j => (List.range 7).all fun d =>
      (cell f (3*j) (3*(12-d))).all (·==transpose (history 12 j (12-d))) := by native_decide

set_option maxHeartbeats 900000 in
theorem birth_tile {u F w P q j i} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (left : 14≤q) (room : q+3≤11+14*u) (jr : j≤1) (lo : q ≤ i+6) (hi : i≤q) :
    maskAtTile F w j i=transpose (history q j i) := by
  let x := q-12
  have off : x+12=q := by dsimp [x]; omega
  let M := fun r c => square F w (1+r) (1+3*x+c)
  have init (r : Nat) (hr : r<16) (c : Nat) (hc : c<37) : M r c∈EastBoundary.Kernel.get G r c := by
    apply chart_mem (m:=M r c) (seed:=true) (L:=12) (R:=0) (j:=2) (b:=8) hr (by omega) (unpack _).1
    · by_cases special : r=0 ∧ c=36
      · simp [special.1,special.2]
      apply Bool.or_eq_true_iff.mpr; right
      have reg := accept_bulk u r (3*x+c) (by omega) (by omega) F acy P S.step w S.clean (by
        intro v loc; apply S.zero; rw [loc]; intro e
        cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at e <;> omega)
      rw [show realTag u (3*x+c)=5+(c+1)%3 by unfold realTag; split_ifs <;> omega] at reg
      change accepts (rowTag r) (5+(c+1)%3) (M r c)=true
      simpa only [M,Nat.add_assoc] using reg
    · by_cases rr : r=0
      swap
      · simp [pins,rr]
      subst r
      by_cases cc : c%3=0
      swap
      · simp [pins,cc]
      have eq : M 0 c=maskAtTile F w 0 (x+c/3) := by
        exact congrArg₂ (square F w) rfl (by omega)
      simp [pins,cc,eq]
      split
      · have b := (unpack (fun s : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+s.val/3:Nat)
            (1+3*(x+c/3)+s.val%3:Nat)))).2 4
        change lane (maskAtTile F w 0 (x+c/3)) 4=(marked F (L7.view w _ 2 (1+3*(x+c/3)+1:Nat))).toNat at b
        rw [b,show 1+3*(x+c/3)+1=2+3*(x+c/3) by omega,S.west (x+c/3) (by omega)]; rfl
      · split
        · rw [show x+c/3=q by omega]; exact S.paid
        · exact S.east _ (by omega) (by omega)
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+3*x+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+3*x+c) false) 80 _ init
  let d := q-i
  have dd : d≤6 ∧ 12-d+x=i := by dsimp [d]; omega
  have res := List.all_eq_true.mp (List.all_eq_true.mp checked j (List.mem_range.mpr (by omega))) d
    (List.mem_range.mpr (by omega))
  have h := beq_iff_eq.mp (List.all_eq_true.mp res _ (live _ (by omega) _ (by omega)))
  have eq : M (3*j) (3*(12-d))=maskAtTile F w j i := congrArg₂ (square F w) rfl (by omega)
  rw [eq] at h; rw [h]; congr 1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp jr with rfl|rfl
  · unfold history seedWord; split_ifs <;> omega
  · rw [eastern (by decide) (by decide) (by omega),eastern (by decide) (by omega) (by omega)]
    unfold mword; split_ifs <;> omega

theorem mark_read {u F w j i m a b} (tile : maskAtTile (u:=u) F w j i=transpose m)
    (bd : m<512) (al : a<3) (bl : b<3) :
    (marked F (L7.view w (35+42*u:Nat) (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat=lane m (3*a+b) := by
  let idx : Fin 9 := ⟨3*b+a,by omega⟩
  have e := (unpack (fun s : Fin 9 => marked F (L7.view w (35+42*u:Nat)
    (1+3*j+s.val/3:Nat) (1+3*i+s.val%3:Nat)))).2 idx
  change lane (maskAtTile F w j i) idx=_ at e
  have swap : ∀ n : Fin 512, ∀ x y : Fin 3, lane (transpose n.val) (3*y.val+x.val)=lane n.val (3*x.val+y.val) := by native_decide
  rw [tile] at e
  exact (by simpa only [idx,show (3*b+a)/3=b by omega,show (3*b+a)%3=a by omega] using e.symm.trans (swap ⟨m,bd⟩ ⟨a,al⟩ ⟨b,bl⟩))

/-- Each column strictly east of the seed has its own north foot.
The birth chart supplies row one at `q`; `first_east` carries it to
the rim, and the eastern fan words carry the individual lines down. -/
theorem north_roots {u F w P q y} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {d : Nat} (pad : d=4 ∨ (d=1 ∧ 35≤q)) (big : 14≤q) (room : q+6≤11+14*u)
    (yl : 4≤y) (mid : 6*y+d≤q+1)
    {i : Nat} (root : q < i) (hi : i<11+14*u) : RootLine F w i y := by
  have first (c : Nat) (lo : q ≤ c) (ch : c<11+14*u) : maskAtTile F w 1 c=73 := by
    induction c,lo using Nat.le_induction with
    | base =>
      rw [birth_tile S acy big (by omega) (by decide) (by omega) le_rfl,
        eastern (by decide) (by omega) (by omega)]
      unfold mword; split_ifs <;> first | rfl | omega
    | succ c hc ih => exact first_east S acy (by omega) hc (by omega) (ih (by omega))
  have tile {j} (jl : 2≤j) (jh : j≤y) : maskAtTile F w j i=73 := by
    rw [rows_restart S acy pad (start:=2) (.inr (by omega)) (by intro r low high; omega)
      j jl (by omega) i (by omega) hi]
    unfold edge; split_ifs <;> omega
  have line (j : Nat) (jl : 4≤j) (jh : j≤y) : RootLine F w i j := by
    induction j,jl using Nat.le_induction with
    | base =>
      apply Short.North.line_from_three S root hi
      intro r low high
      by_cases one : r=1
      · subst r; exact first i (by omega) hi
      · exact tile (j:=r) (by omega) (by omega)
    | succ j low ih =>
      have plain : SouthCap.Strip.GridScan.Rooted.tile F w j i=73 := tile (by omega) (by omega)
      apply SouthCap.Strip.GridScan.Rooted.extend_line (ih (by omega))
      · rw [plain]; decide
      · left; rw [plain]; decide
  exact line y yl le_rfl

private def cutRow (q : Nat) := if 35≤q then q/6 else (q-3)/6

def fits (k q : Nat) : Prop :=
  let y := cutRow q
  53≤k ∧ 14≤q ∧ q+6≤k ∧ 4≤y ∧ Guarded.atCut k q y (q+3-3*y)
instance (k q) : Decidable (fits k q) := by unfold fits; infer_instance

theorem exclude {u F w q P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : fits (11+14*u) q) : False := by
  let y := cutRow q; let B := q+2-3*y; let d := if 35≤q then 1 else 4
  obtain ⟨hk,big,room,yl,ck⟩ := ok
  change 4≤y at yl
  have pad : d=4 ∨ (d=1 ∧ 35≤q) := by dsimp [d]; split <;> omega
  have mid : 6*y+d≤q+1 := by dsimp [d,y,cutRow]; split <;> omega
  have off : B+3*y=q+2 := by dsimp [B]; omega
  have row {j i : Nat} (jl : 2≤j) (jh : j≤y) (il : 3*j+d ≤ i) (ih : i<11+14*u) :=
    rows_restart S acy pad (start:=2) (.inr (by omega)) (by intro r low high; omega)
      j jl (by omega) i il ih
  have plain {i : Nat} (il : B ≤ i) (ih : i<11+14*u) : maskAtTile F w y i=73 := by
    rw [row (by omega) le_rfl (by omega) ih]; unfold edge; split_ifs <;> omega
  apply Guarded.exclude_from H acy one score hk S.room (y:=y) (f:=B+1)
    (by rwa [show B+1=q+3-3*y by omega]) yl (by omega) (by push_cast; omega)
  · refine ⟨fun r lo hi i il ih => (show r=y by omega) ▸ plain (by omega) ih,?_,?_⟩
    · intro t tl th rt
      apply dangling_of_marks _ q y t (by omega) (by omega) (by omega) rt
      intro j jh i a b near it ti _ al bl hm
      by_cases final : j=y
      · subst j
        have v := plateau_bit (plain (i:=i) (by omega) (by omega)) ⟨a,al⟩ ⟨b,bl⟩
        rw [hm] at v
        have az : a=0 := by by_contra! h; simp [h] at v
        unfold NorthFanLines.mark; omega
      apply right_bits q j i a b al bl (by omega) (by omega)
      suffices read : (marked F (L7.view w (35+42*u:Nat) (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat =
          lane (history q j i) (3*a+b) by rw [hm] at read; exact read.symm
      apply mark_read _ _ al bl
      · by_cases early : j≤1
        · exact birth_tile S acy big (by omega) early (by omega) (by omega)
        rw [row (by omega) jh (by omega) (by omega),eastern (by omega) (by omega) (by omega)]
        unfold edge mword; split_ifs <;> rfl
      · by_cases zero : j=0
        · subst j; simp only [history,if_true]; unfold seedWord; split_ifs <;> decide
        rw [eastern (by omega) (by omega) (by omega)]; unfold mword; split_ifs <;> decide
    · intro i _ hi rt
      exact north_roots S acy pad big room yl mid rt hi
  · intro r lo hi i il ih
    obtain rfl : r=y := by omega
    exact plain (by omega) ih
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.ShortBirth
