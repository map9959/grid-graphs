import GridGraphs.ResidueTwoUpper.OneGap.FanBulkBits
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
open ResidueZero Stencil L7 FanSlab FanSeed

private theorem bdCoords {n} (w : View) (p : GridVertex n n) : IsGridBoundary p ↔ (coordinates w p).1=0 ∨ (coordinates w p).2=0 ∨
    (coordinates w p).1=n-1 ∨ (coordinates w p).2=n-1 := by
  have a := p.1.isLt; have b := p.2.isLt
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [IsGridBoundary,coordinates,reflect,coord] <;> omega

theorem dir_lt {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (Q : Flow F) (price : Prices F w) (r c : Nat)
    (rr : 8≤r ∧ r+7≤33+42*u) (cc : 8≤c ∧ c+7≤33+42*u) : arrow Q.parent w (r,c)<4 := by
  obtain ⟨z,edge⟩ := bulk_active u F w price r c rr cc
  have inp : In (N u) (r,c) := by dsimp [In,N]; omega
  have ne : ((r:Int),(c:Int))≠coordinates w (Q.parent (point u w (r,c))) := by
    intro eq; have fix := point_inj w (eq.symm.trans (coords_point inp).symm)
    have bd := (bdCoords w _).mp (Q.active _ _ edge fix); rw [coords_point inp] at bd; dsimp [N] at bd; omega
  unfold arrow way; rw [if_neg ne]; split_ifs <;> decide

theorem root_tip {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (Q : Flow F) (y t : Nat)
    (row : 1+3*y+1<N u) (col : 1+3*t+1<N u) (line : RootLine F w t y) : arrow Q.parent w (1+3*(y:Int),1+3*(t:Int))=3 := by
  let c := 1+3*t; let d := 1+3*y; let v (r : Nat) := point u w ((r:Int),(c:Int))
  have C (r : Nat) (hr : r≤d) : coordinates w (v r)=((r:Int),(c:Int)) := coords_point (by dsimp [In,c,d,N] at *; omega)
  have E (r : Nat) (hr : r<d) : (Bonds F).Adj (v r) (v (r+1)) := by
    constructor
    · rw [adj_iff w,C r (by omega),C (r+1) (by omega)]; simp
    · have H := line r hr
      have bit (s : Nat) (hs : s≤d) : marked F (L7.view w (N u) s c)=decide (v s∈F) := by
        rw [←marked_at F (v s),←coords_view w (v s),C s hs]
      rw [bit r (by omega),bit (r+1) (by omega)] at H; simpa using H
  have previous (r : Nat) (hr : r<d) : Q.parent (v (r+1))=v r := by
    induction r with
    | zero =>
      apply (Q.covers _ _ (E 0 hr).symm).mpr; intro bad
      have z := Q.noExit _ ((bdCoords w _).mpr (.inl (by rw [C 0 (by omega)]; rfl)))
      rw [bad] at z; have z := (bdCoords w _).mp z; rw [C 1 (by omega)] at z; dsimp [c,d,N] at *; omega
    | succ r ih =>
      apply (Q.covers _ _ (E _ hr).symm).mpr; rw [ih (by omega)]; intro eq
      have z := congrArg (coordinates w) eq; have hx := congrArg Prod.fst z; rw [C _ (by omega),C _ (by omega)] at hx; dsimp at hx; omega
  let p : Pos := (1+3*(y:Int),1+3*(t:Int)); change arrow Q.parent w p=(3:Fin 4).val
  have Row : 1+3*(y:Int)+1<(N u:Int) := by exact_mod_cast row
  have Col : 1+3*(t:Int)+1<(N u:Int) := by exact_mod_cast col
  apply (going Q.step 3 (by dsimp [p,In,N] at *; omega) (by change In _ (1+3*(y:Int)-1,1+3*(t:Int)); dsimp [In,N] at ⊢; dsimp [N] at Row Col; omega)).mpr
  have v1 : p=(((3*y+1:Nat):Int),(c:Int)) := by ext <;> dsimp [p,c]; push_cast <;> omega
  have v2 : shift p 3=(((3*y:Nat):Int),(c:Int)) := by apply Prod.ext <;> simp [shift,p,c] <;> ring
  change Q.parent (point u w p)=point u w (shift p 3); rw [v2,v1]; exact previous (3*y) (by dsimp [d]; omega)

theorem dangling_tip {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (Q : Flow F) (q y t : Nat)
    (row : 1+3*y+2<N u) (col : 2≤1+3*t ∧ 1+3*t+2<N u) (birth : 2≤(q:Int)-t+3 ∧ (q:Int)-t+3≤1+3*(y:Int))
    (upper : Seal F w q t y) (tile : square F w (1+3*y) (1+3*t)=73) : arrow Q.parent w (1+3*(y:Int),1+3*(t:Int))≠3 := by
  let d := 1+3*(y:Int); let c := 1+3*(t:Int); let p : Pos := (d,c)
  have Row : 1+3*(y:Int)+2<(N u:Int) := by exact_mod_cast row
  have Col : 2≤1+3*(t:Int) ∧ 1+3*(t:Int)+2<(N u:Int) := by exact_mod_cast col
  have hin : In (N u) p := by dsimp [p,d,c,In,N] at *; omega
  have s : coordinates w (point u w p)=p := coords_point hin
  let S : Set (GridVertex (N u) (N u)) := {v | (coordinates w v).1≤d}
  let v : S := ⟨point u w p,by change (coordinates w _).1≤d; rw [s]⟩
  have on : onLine ((q:Int)-t+3) d c (coordinates w v.1) := by change onLine _ _ _ (coordinates w (point u w p)); rw [s]; exact ⟨rfl,birth.2,le_rfl⟩
  have sep (x : S) (hl : ((Bonds F).induce S).Reachable v x) := sealed F w _ d c birth.1 (by dsimp [d,N] at *; omega)
    (by dsimp [c,N] at *; omega) upper.1 upper.2 v on x hl
  have marked' := plateau_bit tile 0 0
  have vm : v.1∈F := by
    change point u w p∈F; have pos := coord_point (w:=w) hin
    apply of_decide_eq_true; rw [←marked_at, pos]; simpa [p,c,d] using marked'
  have nxt : In (N u) (shift p 1) := by change In _ (d+1,c); dsimp [In,d,c,N]; dsimp [N] at Row Col; omega
  have adj : (gridGraph _ _).Adj v.1 (point u w (shift p 1)) := by rw [adj_iff w,s,coords_point nxt]; simp [shift]
  have out := forced_exit Q S v ⟨_,adj,Or.inl vm⟩ (fun x hl => (sep x hl).1) (fun x hl z e hz => by
    have h := ((sep x hl).2 z e (by change ¬(coordinates w z).1≤d at hz; omega)).1
    apply Subtype.ext; apply point_inj w; exact h.trans s.symm)
  intro north
  have inn : In (N u) (shift p 3) := by change In _ (d-1,c); dsimp [In,d,c,N]; dsimp [N] at Row Col; omega
  have eq := (going (w:=w) Q.step 3 hin inn).mp north
  apply out; change (coordinates w (Q.parent (point u w p))).1≤d; change Q.parent (point u w p)=point u w (shift p 3) at eq; rw [eq,coords_point inn]; change d-1≤d; omega
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
