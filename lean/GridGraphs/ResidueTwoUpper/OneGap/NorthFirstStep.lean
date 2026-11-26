import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open ResidueZero Stencil L7 FanSweep FanSlab Short

private def tbl := Array.ofFn fun r : Fin 8 => Array.ofFn fun c : Fin 13 =>
  (List.range 512).filter (accepts r.val c.val)
private def span (d : Nat) := 3*min 5 (d-1)
private def chart1 (d : Nat) := build ⟨15,span d,[]⟩ fun r c =>
  if r=0 ∧ c=0 then [64,72] else
    ((tbl[rowTag r]!)[realTag 0 (3*(11-d)+c)]!).filter fun m =>
      (r != 0 || c%3 != 0 || m==72) && (r != 3 || c != 0 || m==73)
private def test (d : Nat) :=
  (cell (Kernel.prune 16 (span d+1) 48 (chart1 d)) 3 3).all (·==73)
private theorem tested : (List.range 7).all (fun j => test (j+2)) := by native_decide

set_option maxHeartbeats 900000 in
/-- The northern seed masks carry a row-one 73 all the way east.
The window shortens at the true rim and retains its price tags. -/
theorem first_east {u F w P q i} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (il : 2 ≤ i) (lo : q ≤ i) (ih : i+2≤11+14*u)
    (prev : maskAtTile F w 1 i=73) : maskAtTile F w 1 (i+1)=73 := by
  let d := min 8 (11+14*u-i)
  have bounds : 2≤d ∧ d≤8 := by dsimp [d]; omega
  let M := fun r c => square F w (1+r) (1+3*i+c)
  have keep (r : Nat) (hr : r<16) (c : Nat) (hc : c<span d+1) :
      M r c∈EastBoundary.Kernel.get (chart1 d) r c := by
    have fit : c≤3*(11+14*u-i-1) ∧ c≤15 := by dsimp [span,d] at hc; omega
    have align (z : r=0) (cc : c%3=0) : M r c=maskAtTile F w 0 (i+c/3) := by
      exact congrArg₂ (square F w) (by omega) (by omega)
    simp only [EastBoundary.Kernel.get,chart1,build]
    by_cases corner : r=0 ∧ c=0
    · obtain ⟨rfl,rfl⟩ := corner
      have eq := align rfl rfl
      by_cases paid : i=q
      · subst i; simp [eq,S.paid,maskAtTile]
      · simp [eq,S.east i (by omega) (by omega),maskAtTile]
    · have A := accept_bulk u r (3*i+c) (by omega) (by omega) F acy P S.step w S.clean (by
        intro v loc; apply S.zero; rw [loc]; intro e
        cases w with | mk a b s => cases a <;> cases b <;> cases s <;>
          simp [L7.view,reflect] at e <;> omega)
      have tag : realTag u (3*i+c)=realTag 0 (3*(11-d)+c) := by
        unfold realTag; dsimp [d]; split_ifs <;> omega
      rw [tag] at A
      have good : accepts (rowTag r) (realTag 0 (3*(11-d)+c)) (M r c) := by
        simpa only [M,Nat.add_assoc] using A
      have rt : rowTag r<8 := by unfold rowTag; split <;> omega
      have ct : realTag 0 (3*(11-d)+c)<13 := by unfold realTag; dsimp [span] at hc; split_ifs <;> omega
      have bd : M r c<512 := (unpack _).1
      have top : r=0 → c%3=0 → M r c=72 := by
        intro rr cc; rw [align rr cc]; exact S.east _ (by omega) (by omega)
      have west : r=3 → c=0 → M r c=73 := by rintro rfl rfl; exact prev
      have pins : ((r != 0 || c%3 != 0 || M r c==72) && (r != 3 || c != 0 || M r c==73))=true := by
        apply Bool.and_eq_true_iff.mpr; constructor
        · by_cases rr : r=0 <;> by_cases cc : c%3=0 <;> simp [rr,cc]
          simpa only [rr] using top rr cc
        · by_cases rr : r=3 <;> by_cases cc : c=0 <;> simp [rr,cc]
          simpa only [rr,cc] using west rr cc
      simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq] at pins
      simp [hr,hc,corner,tbl,rt,ct,bd,good]
      exact pins
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+3*i+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+3*i+c) false) 48 _ keep
  have ck := List.all_eq_true.mp tested (d-2) (List.mem_range.mpr (by omega))
  rw [show d-2+2=d by omega] at ck
  have h := beq_iff_eq.mp (List.all_eq_true.mp ck _ (live 3 (by decide) 3 (by dsimp [span]; omega)))
  exact (show M 3 3=maskAtTile F w 1 (i+1) from congrArg₂ (square F w) rfl (by omega)) ▸ h
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
