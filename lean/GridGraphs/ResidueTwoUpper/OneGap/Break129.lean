import GridGraphs.ResidueTwoUpper.OneGap.LatchedBand

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Break129
open ResidueZero L7 FanSlab BoundarySix.Connected SouthCap SouthCap.Strip
open SouthCap.Strip.GridScan SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan.Rooted.Buffered

private def law (e : Nat) (w : Word) : Prop :=
  let (a,b,c,d) := w
  (a=129 → b=9 → e≤9 ∧ ((c=18 ∧ d=18) ∨ (c=146 ∧ d=146))) ∧
  (a=9 → b=73 → c≠18 ∧ (c=146 → d=144)) ∧
  (a=73 → b=73 → (c=144 → d=129) ∧ (c=129 → d=9 ∨ d=73)) ∧
  (a=144 → b=129 → d=18 ∨ d=146) ∧ (a=129 → b=73 → c=128) ∧
  (b=129 → d=128 → a=16 ∧ c=292) ∧ (b=73 → d=129 → c=16 → a=16)
set_option synthInstance.maxSize 2048 in
private instance (e w) : Decidable (law e w) := by
  obtain ⟨a,b,c,d⟩ := w
  dsimp only [law]
  infer_instance
private theorem check : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law (6+e.val) w))=true := by native_decide

section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy score hk
private theorem physical {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    law (endTag K c) (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have z := check ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at z
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at z
  exact of_decide_eq_true (List.all_eq_true.mp z _ (board_word H acy score hk rl cl rh ch))

include one
set_option maxHeartbeats 1500000 in
/-- The 129,9 edge is forced three columns east per row. It cannot
terminate in a 73 against the western 144, reach the east fringe,
or leave the north line attached to the south rim. -/
theorem no_fast_tail {r x : Nat} (rl : 4≤r) (cl : 4≤x) (rh : r+2≤K) (ch : x+2≤K)
    (a : t r x=129) (b : t r (x+1)=9)
    (plain : ∀ i, x+2 ≤ i → i < K → t r i=73) (root : RootLine F v (K-1) r) : False := by
  induction rem : K-r using Nat.strong_induction_on generalizing r x
  rename_i rem ih
  subst rem
  have ruleAt := @physical u F v q H acy score hk
  have z := (ruleAt rl cl rh ch).1 a b
  have room : x+5≤K := by
    have e := z.1
    unfold endTag at e; split at e <;> omega
  have p (d : Nat) (h : d≤2) := plain (x+2+d) (by omega) (by omega)
  have n := (ruleAt rl (by omega : 4≤x+1) rh (by omega)).2.1 b (p 0 (by decide))
  have m := (ruleAt rl (by omega : 4≤x+2) rh (by omega)).2.2.1 (p 0 (by decide)) (p 1 (by decide))
  have s := (ruleAt rl (by omega : 4≤x+3) rh (by omega)).2.2.1 (p 1 (by decide)) (p 2 (by decide))
  have mid := n.2 ((z.2.resolve_left (fun h => n.1 h.2)).2)
  have tip := m.1 mid
  have head := s.2 tip
  have last := plain (K-1) (by omega) (by omega)
  have next := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
  have east : ∀ i, x+4 ≤ i → i < K → t (r+1) i=9 ∨ t (r+1) i=73 := by
    intro i l h
    induction i,l using Nat.le_induction with
    | base => exact head
    | succ i il ih =>
      have A := plain i (by omega) (by omega)
      have B := plain (i+1) (by omega) h
      have row : BandRow t r i K := by
        intro c l hc
        rw [plain c (by omega) (by omega),plain (c+1) (by omega) (by omega)]; decide
      have ed : edge₃ (t r i) (t (r+1) i) := by
        rw [A]; rcases ih (by omega) with E|E <;> rw [E] <;> decide
      have E := (across H acy score hk rl (by omega) rh row ed).2 (i+1) (by omega) h
      rw [B] at E
      simpa [edge₃] using E
  by_cases bottom : r+2=K
  · have E := east (K-1) (by omega) (by omega)
    rw [show r+1=10+14*u by omega] at E next
    apply no_south_middle H acy one (by omega) (by omega) next
    rcases E with A|A <;> rw [A] <;> decide
  have keep : t (r+1) (x+4)=9 := by
    rcases head with A|A
    · exact A
    have clash := (ruleAt (by omega : 4≤r+1) (by omega : 4≤x+2) (by omega) (by omega)).2.2.2.1 mid tip
    have other := (ruleAt (by omega : 4≤r+1) (by omega : 4≤x+3) (by omega) (by omega)).2.2.2.2.1 tip A
    change t (r+1+1) (x+3)=128 at other
    change t (r+1+1) (x+3)=18 ∨ t (r+1+1) (x+3)=146 at clash
    omega
  have row : BandRow t (r+1) (x+4) K := by
    intro i l h
    apply physical_pair H acy score hk (by omega) (by omega) (by omega) h
    · rcases east i l (by omega) with A|A <;> rw [A] <;> decide
    · rcases east (i+1) (by omega) (by omega) with A|A <;> rw [A] <;> decide
  apply ih (K-(r+1)) (by omega) (r:=r+1) (x:=x+3) (by omega) (by omega) (by omega) (by omega) tip keep _ next rfl
  intro i l h
  have reg := rigid H acy one score hk (by omega) (by omega) (by omega) (by omega : x+4+2≤K) row next i (by omega) h
  rcases reg with E|⟨E,_⟩ <;> solve | exact E | omega

set_option maxHeartbeats 1000000 in
/-- A 73→129 break below a plain suffix is possible only beside a
particular western column. Rows are given in physical order. -/
theorem forced_corner {r x : Nat} (rl : 4≤r) (cl : 5≤x) (rh : r+3≤K) (ch : x+3≤K)
    (plain : ∀ i, x ≤ i → i < K → t r i=73) (hit : t (r+1) x=129)
    (root : RootLine F v (K-1) r) :
    t (r+1) (x+1)=73 ∧ t (r+2) x=128 ∧
      t r (x-1)=16 ∧ t (r+1) (x-1)=16 ∧ t (r+2) (x-1)=292 := by
  have ruleAt := @physical u F v q H acy score hk
  have A := plain x le_rfl (by omega)
  have B := plain (x+1) (by omega) (by omega)
  have h := (ruleAt rl (by omega : 4≤x) (by omega) (by omega)).2.2.1 A B |>.2 hit
  have last := plain (K-1) (by omega) (by omega)
  have next := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
  have right : t (r+1) (x+1)=73 := by
    rcases h with m|m
    · exfalso
      have row : BandRow t r (x+1) K := by
        intro i l h'; rw [plain i (by omega) (by omega),plain (i+1) (by omega) (by omega)]; decide
      have ed : edge₃ (t r (x+1)) (t (r+1) (x+1)) := by rw [B,m]; decide
      have lower := (across H acy score hk rl (by omega) (by omega) row ed).1
      have reg := rigid H acy one score hk (by omega) (by omega) (by omega) (by omega) lower next
      apply no_fast_tail H acy one score hk (by omega) (by omega) (by omega) (by omega) hit m _ next
      intro i l h'
      rcases reg i (by omega) h' with e|⟨e,_⟩ <;> solve | exact e | omega
    · exact m
  have below := (ruleAt (by omega : 4≤r+1) (by omega : 4≤x) (by omega) (by omega)).2.2.2.2.1 hit right
  have W := (ruleAt (by omega : 4≤r+1) (by omega : 4≤x-1) (by omega) (by omega)).2.2.2.2.2.1
  have V := (ruleAt rl (by omega : 4≤x-1) (by omega) (by omega)).2.2.2.2.2.2
  rw [show x-1+1=x by omega] at W V
  have l := W hit below
  exact ⟨right,below,V A hit l.1,l⟩
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Break129
