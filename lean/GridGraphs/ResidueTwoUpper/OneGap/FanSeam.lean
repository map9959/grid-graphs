import GridGraphs.ResidueTwoUpper.OneGap.FanTips

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
open L7 FanSlab FanSeed Stencil ResidueZero

/-- On either type of line the two off-center arrows cannot go north:
a mark just above them would be diagonal to a mark on this or the next
line. Only the center arrow depends on the root/dangling history. -/
theorem off_tip {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (Q : Flow F) (price : Prices F w)
    (y i : Nat) (row : 3≤y ∧ y+5≤11+14*u) (col : 3≤ i ∧ i+5≤11+14*u)
    (tile : square F w (1+3*y) (1+3*i)=73) (next : square F w (1+3*y) (1+3*(i+1))=73) (a : Fin 3) (nz : a.val≠0) :
    arrow Q.parent w (1+3*(y:Int),1+3*(i:Int)+a.val)≠3 := by
  let R := 3*y; let C := 1+3*i+a.val-1; let m := square F w R C
  have good := price R C (by dsimp [R]; omega) (by dsimp [R]; omega) (by dsimp [C]; omega) (by dsimp [C]; omega)
  have ck : ∀ r c : Fin 3, ∀ m : Fin 512, accepts (5+r.val) (5+c.val) m →
      (lane m 3=1 ∨ lane m 5=1) → lane m 1=0 := by native_decide
  let pt : Pos := (1+3*(y:Int),1+3*(i:Int)+a.val)
  have h0 : In (N u) pt := by dsimp [In,pt,N]; omega
  have h1 : In (N u) (shift pt 3) := by change In _ (1+3*(y:Int)-1,1+3*(i:Int)+a.val); dsimp [In,N]; omega
  have read (k : Fin 9) : lane m k=(marked F (L7.view w (N u) (R+k.val/3:Nat) (C+k.val%3:Nat))).toNat := (unpack _).2 k
  have val := ck ⟨R%3,by omega⟩ ⟨C%3,by omega⟩ ⟨m,(unpack _).1⟩ good (by
    by_cases a1 : a.val=1
    · left; change lane m ((3:Fin 9).val)=1; rw [read]; have h := plateau_bit tile 0 0
      change (marked F (L7.view w _ (1+3*y+0:Nat) (1+3*i+0:Nat))).toNat=1 at h
      change (marked F (L7.view w _ (R+1:Nat) (C+0:Nat))).toNat=1
      simpa only [show R+1=1+3*y+0 by dsimp [R]; omega,show C+0=1+3*i+0 by dsimp [C]; omega] using h
    · right; change lane m ((5:Fin 9).val)=1; rw [read]; have h := plateau_bit next 0 0
      change (marked F (L7.view w _ (1+3*y+0:Nat) (1+3*(i+1)+0:Nat))).toNat=1 at h
      change (marked F (L7.view w _ (R+1:Nat) (C+2:Nat))).toNat=1
      simpa only [show R+1=1+3*y+0 by dsimp [R]; omega,show C+2=1+3*(i+1)+0 by dsimp [C]; have := a.isLt; omega] using h)
  change lane m ((1:Fin 9).val)=0 at val; rw [read] at val
  have here := plateau_bit tile a 0
  intro north; have par := (going (w:=w) Q.step 3 h0 h1).mp north
  change Q.parent (point u w pt)=point u w (shift pt 3) at par
  have ne : Q.parent (point u w pt)≠point u w pt := by
    intro fix; rw [fix] at par; have e := congrArg (fun z => (coordinates w z).1) par
    change (coordinates w (point u w pt)).1=(coordinates w (point u w (shift pt 3))).1 at e; rw [coords_point h0,coords_point h1] at e; change pt.1=pt.1-1 at e; omega
  have edge := (Q.step _ ne).2; rw [par] at edge
  have z : bitAt F w pt=false := by simpa [pt,bitAt,nz] using here
  have h : bitAt F w (shift pt 3)=false := by
    change (marked F (L7.view w (N u) (R+0:Nat) (C+1:Nat))).toNat=0 at val
    simpa [bitAt,pt,R,shift,show C+1=1+3*i+a.val by dsimp [C]; omega] using val
  simp only [bitAt,←coord_point (w:=w) h0,←coord_point (w:=w) h1,marked_at,decide_eq_false_iff_not] at z h
  exact edge.elim z h
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
