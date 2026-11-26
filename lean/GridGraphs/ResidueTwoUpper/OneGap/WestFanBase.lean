import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open ResidueZero Stencil L7 FanSweep FanSlab Short

private def prices := Array.ofFn fun a : Fin 8 => Array.ofFn fun c : Fin 8 =>
  (List.range 512).filter (accepts a.val c.val)
private def westGrid := build ⟨24,66,[]⟩ fun r c =>
  ((prices[rowTag r]!)[if c<5 then c else 5+(c+1)%3]!).filter fun m =>
    r != 0 || c%3 != 0 || lane m 4==1
private def baseTest (j : Nat) :=
  let g := Kernel.prune 25 67 128 westGrid
  (List.range 3).all fun i => (cell g (3*j) (3*(3*j+1+i))).all (·==146)
private theorem base_checked : baseTest 2 && baseTest 3 := by native_decide

set_option maxHeartbeats 800000 in
theorem west_base {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    (big : 35≤q) {j i : Nat} (row : j=2 ∨ j=3) (lo : 3*j+1 ≤ i) (hi : i<3*j+4) :
    maskAtTile F w j i=146 := by
  let M := fun r c => square F w (1+r) (1+c)
  have room := S.room
  have initial (r : Nat) (hr : r<25) (c : Nat) (hc : c<67) : M r c∈Kernel.get westGrid r c := by
    have reg := accept_bulk u r c (by omega) (by omega) F acy P S.step w S.clean (by
      intro v loc; apply S.zero; rw [loc]; intro e
      cases w with | mk a b s => cases a <;> cases b <;> cases s <;>
        simp [L7.view,reflect] at e <;> omega)
    rw [show realTag u c=(if c<5 then c else 5+(c+1)%3) by unfold realTag; split_ifs <;> omega] at reg
    have bd : M r c<512 := (unpack _).1
    have tagged : rowTag r<8 := by unfold rowTag; split <;> omega
    have ct : (if c<5 then c else 5+(c+1)%3)<8 := by split <;> omega
    have pin : r != 0 || c%3 != 0 || lane (M r c) 4==1 := by
      by_cases rr : r=0 <;> by_cases cc : c%3=0 <;> simp [rr,cc]
      subst r
      have m := (unpack (fun s : Fin 9 => marked F (L7.view w (35+42*u:Nat)
        (1+0+s.val/3:Nat) (1+c+s.val%3:Nat)))).2 (4 : Fin 9)
      change lane (M 0 c) 4=(marked F (L7.view w _ (2:Nat) (1+c+1:Nat))).toNat at m
      rw [m,show 1+c+1=2+3*(c/3) by omega]
      exact congrArg Bool.toNat (S.west (c/3) (by omega))
    simpa [Kernel.get,westGrid,build,prices,hr,hc,tagged,ct,pin,bd,show accepts _ _ (M r c) from reg]
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) false) 128 _ initial
  have test : baseTest j := row.elim (fun e => e ▸ (Bool.and_eq_true_iff.mp base_checked).1)
    (fun e => e ▸ (Bool.and_eq_true_iff.mp base_checked).2)
  have hit := List.all_eq_true.mp test (i-(3*j+1)) (List.mem_range.mpr (by omega))
  rw [show 3*j+1+(i-(3*j+1))=i by omega] at hit
  exact beq_iff_eq.mp (List.all_eq_true.mp hit _ (live _ (by omega) _ (by omega)))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
