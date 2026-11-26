import GridGraphs.ResidueTwoUpper.OneGap.CornerCone

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CornerCone
open ResidueZero BoundarySix.Connected SouthCap SouthCap.Strip SouthCap.Strip.GridScan
open SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan.Rooted.Buffered

private def law (w : Word) : Prop :=
  let (a,b,c,d) := w
  ((a=2 ∨ a=3) → b=9 → d=3 ∨ d=7) ∧
    (a=9 → b=73 → c≠7 ∧ (d=9 → c=2 ∨ c=3) ∧ (d=9 ∨ d=73 ∨ d=144)) ∧
    (a=129 → b=73 → d=9 ∨ d=73) ∧ (a=16 → b=73 → d=129 ∨ d=73)
set_option synthInstance.maxSize 2048 in
private instance (w) : Decidable (law w) := by unfold law; infer_instance
private theorem checked : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law w))=true := by native_decide
section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy score hk
private theorem ruleAt {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    law (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := checked ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))
include one
theorem no_end9 {r x : Nat} (rl : 4≤r) (cl : 4≤x) (rh : r+3≤K) (ch : x+3≤K)
    (cap : t r x=2 ∨ t r x=3) (nine : t r (x+1)=9)
    (plain : ∀ i, x+2 ≤ i → i < K → t r i=73) (root : RootLine F v (K-1) r) : False := by
  have L := (ruleAt H acy score hk rl cl (by omega) (by omega)).1 cap nine
  have N := (ruleAt H acy score hk rl (by omega : 4≤x+1) (by omega) (by omega)).2.1 nine
    (plain _ le_rfl (by omega))
  have three := L.resolve_right N.1
  have ed : edge₃ (t r (x+1)) (t (r+1) (x+1)) := by rw [nine,three]; decide
  have row : BandRow t r (x+1) K := by
    intro i l h
    rw [plain (i+1) (by omega) (by omega)]
    by_cases E : i=x+1
    · rw [E,nine]; decide
    · rw [plain i (by omega) (by omega)]; decide
  have last := plain (K-1) (by omega) (by omega)
  exact no_latch H acy one score hk (by omega) (by omega) (by omega) (by omega)
    (across H acy score hk rl (by omega) (by omega) row ed).1 (.inl three)
    (extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide)))

private def rank (m : Nat) := if m=16 then 3 else if m=129 then 2 else if m=9 then 1 else 0
private def head (m : Nat) := m=9 ∨ m=16 ∨ m=129 ∨ m=73
omit H acy one score hk in
private theorem rank0 {m : Nat} (h : head m) (z : rank m=0) : m=73 := by
  rcases h with rfl|rfl|rfl|rfl <;> simp [rank] at *

omit H acy one score hk in
private theorem head_ne {m : Nat} (h : head m) : m≠144 := by
  rcases h with rfl|rfl|rfl|rfl <;> decide

set_option maxHeartbeats 650000 in
/-- Along the one-column-per-row diagonal a head of type 16 can pass
to 129, then to 9. A second advancing 9 would force a latch in the
next row. Once at 73 the diagonal stays at 73. -/
private theorem dec {r x : Nat} (rl : 4≤r) (cl : 5≤x) (rh : r+4≤K) (ch : x+5≤K)
    (A : head (t r x)) (plain : ∀ i, x+1 ≤ i → i < K → t r i=73)
    (root : RootLine F v (K-1) r) :
    head (t (r+1) (x+1)) ∧ rank (t (r+1) (x+1))≤rank (t r x)-1 := by
  have src := step_head H acy one score hk rl (by omega) (by omega) (by omega) plain root
  have L := ruleAt H acy score hk rl (by omega : 4≤x) (by omega) (by omega)
  have B := plain (x+1) le_rfl (by omega)
  refine ⟨src.1,?_⟩
  rcases A with m|m|m|m
  · have out := L.2.1 m B
    have last := plain (K-1) (by omega) (by omega)
    have next := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
    rcases out.2.2 with n|n|n
    · exact (no_end9 H acy one score hk (by omega) (by omega) (by omega) (by omega)
        (out.2.1 n) n src.2 next).elim
    · rw [m,n]; decide
    · exact (head_ne (m:=t (r+1) (x+1)) src.1 n).elim
  · rcases L.2.2.2 m B with n|n <;> rw [m,n] <;> decide
  · rcases L.2.2.1 m B with n|n <;> rw [m,n] <;> decide
  · have wider : ∀ i, x ≤ i → i < K → t r i=73 := by
      intro i l h; rcases Nat.eq_or_lt_of_le l with rfl|lt
      · exact m
      · exact plain i (by omega) h
    have out := (step_head H acy one score hk rl cl (by omega) (by omega) wider root).2 (x+1) le_rfl (by omega)
    rw [out,m]; decide

/-- A known low-rank head pays for the next descent: the plain suffix
starts at the same column below it as above it. -/
theorem low_head {r x : Nat} (rl : 4≤r) (cl : 5≤x) (rh : r+4≤K) (ch : x+5≤K)
    (A : t r x=9 ∨ t r x=73) (plain : ∀ i, x+1 ≤ i → i < K → t r i=73)
    (root : RootLine F v (K-1) r) :
    ∀ i, x+1 ≤ i → i<K → t (r+1) i=73 := by
  have h : head (t r x) := A.imp_right (fun m => Or.inr (Or.inr m))
  obtain ⟨B,bound⟩ := dec H acy one score hk rl cl rh ch h plain root
  have rk : rank (t r x)≤1 := by rcases A with m|m <;> rw [m] <;> decide
  intro i lo hi
  rcases Nat.eq_or_lt_of_le lo with rfl|more
  · exact rank0 B (by omega)
  · exact (step_head H acy one score hk rl (by omega) (by omega) (by omega) plain root).2 i (by omega) hi

/-- Four descents cost at most three western columns. No prescribed
parent direction or shape assumption on the western exterior. -/
theorem four {r a : Nat} (rl : 4≤r) (cl : 5≤a) (rh : r+7≤K) (ch : a+8≤K)
    (plain : ∀ i, a ≤ i → i < K → t r i=73) (root : RootLine F v (K-1) r) :
    ∀ i, a+3 ≤ i → i < K → t (r+4) i=73 := by
  have states (j : Nat) (jh : j≤4) := cone H acy one score hk (D:=4) (f:=K-1)
    rl cl (by omega) (by omega) (by omega) plain
    (fun i l h => by rwa [show i=K-1 by omega]) (by omega) j jh
  have first := (step_head H acy one score hk rl cl (by omega) (by omega) plain root).1
  have path (j : Nat) (jh : j≤3) : head (t (r+1+j) (a+j)) ∧ rank (t (r+1+j) (a+j))≤3-j := by
    induction j with
    | zero =>
      refine ⟨first,?_⟩
      unfold rank; split_ifs <;> omega
    | succ j ih =>
      obtain ⟨prev,bound⟩ := ih (by omega)
      have pre := states (1+j) (by omega)
      rw [show r+(1+j)=r+1+j by omega,show a+(1+j)=a+j+1 by omega] at pre
      have out := dec H acy one score hk (r:=r+1+j) (x:=a+j) (by omega) (by omega)
        (by omega) (by omega) prev pre.1 (pre.2 (K-1) le_rfl (by omega))
      exact ⟨out.1,by change rank (t (r+1+j+1) (a+j+1))≤3-(j+1); have := out.2; omega⟩
  intro i l h
  by_cases E : i=a+3
  · subst i
    exact rank0 (path 3 (by decide)).1 (Nat.eq_zero_of_le_zero (path 3 (by decide)).2)
  · exact (states 4 le_rfl).1 i (by omega) h

/-- Retain the same rooted columns through arbitrarily many four-row
steps. Only the three intermediate rows need the elementary cone. -/
theorem blocks {y a f s : Nat} (yl : 4≤y) (al : 5≤a) (yh : y+4*s+3≤K)
    (space : a+3*s+5≤K) (buf : a+3*s≤f) (ft : f<K)
    (plain : ∀ i, a ≤ i → i < K → t y i=73)
    (roots : ∀ i, f ≤ i → i < K → RootLine F v i y) :
    (∀ i, a+3*s ≤ i → i < K → t (y+4*s) i=73) ∧
      ∀ i, f ≤ i → i < K → RootLine F v i (y+4*s) := by
  induction s with
  | zero => exact ⟨plain,roots⟩
  | succ s ih =>
    obtain ⟨top,lines⟩ := ih (by omega) (by omega) (by omega)
    rw [show y+4*(s+1)=y+4*s+4 by omega,show a+3*(s+1)=a+3*s+3 by omega]
    refine ⟨four H acy one score hk (by omega) (by omega) (by omega) (by omega) top
      (lines (K-1) (by omega) (by omega)),?_⟩
    have mid := cone H acy one score hk (D:=3) (by omega) (by omega) (by omega)
      (by omega) (by omega) top lines ft 3 le_rfl
    intro i lo hi
    have m := mid.1 i (by omega) hi
    exact extend_line (y:=y+4*s+3) (mid.2 i lo hi) (by rw [m]; decide) (.inl (by rw [m]; decide))
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CornerCone
