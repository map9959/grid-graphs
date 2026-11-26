import GridGraphs.NoPitch.TailRows.IncidenceViews

namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset TailRows TailRows.Incidence
variable {k : Nat}

theorem moved_small {n m h} (p : Board n) (q : Board m) {r c dn : Int}
    (H : h=7 ∨ h=8) (res : (n+h)%3=0) (big : 20≤n) (R : (q.1.val:Int)=p.1.val+r)
    (C : (q.2.val:Int)=p.2.val+c) (D : (m:Int)=n+dn)
    (bound : -2≤r ∧ r≤2 ∧ -2≤c ∧ c≤2 ∧ -2≤r-dn ∧ r-dn≤2 ∧ -2≤c-dn ∧ c-dn≤2) :
    moved h (fine n h p.1 p.2) r c dn=coarse q := by
  have ax (z : Fin n) (w : Fin m) (u : Int) (a : (w.val:Int)=z.val+u)
      (b : -2≤u ∧ u≤2 ∧ -2≤u-dn ∧ u-dn≤2) : axisMove h (axis n h z) u dn=axis m 4 w := by
    have := z.isLt; have := w.isLt
    unfold axisMove axis; split_ifs <;> push_cast <;> split_ifs <;> omega
  have diag (a t : Int) (ht : -5≤t ∧ t≤5) : cl4 ((clip a:Int)-9+t)=cl4 (a+t) := by
    unfold cl4 clip; omega
  simp only [moved,fine,List.getElem!_cons_zero,List.getElem!_cons_succ,coarse]
  congr 1
  · exact ax _ _ _ R (by omega)
  congr 1
  · exact ax _ _ _ C (by omega)
  have d := diag ((p.1.val:Int)-p.2.val) (r-c) (by omega)
  have a := diag ((p.1.val:Int)+p.2.val+1-n) (r+c-dn) (by omega)
  change [cl4 _,cl4 _]=[cl4 _,cl4 _]
  rw [show (q.1.val:Int)-q.2.val=(p.1.val:Int)-p.2.val+(r-c) by omega,
      show (q.1.val:Int)+q.2.val+1-m=(p.1.val:Int)+p.2.val+1-n+(r+c-dn) by omega,←d,←a]
  congr 2 <;> ring_nf
theorem valid_small {n m h} (p : Board n) {r c dn : Int}
    (H : h=7 ∨ h=8) (big : 20≤n) (D : (m:Int)=n+dn)
    (bound : -2≤r ∧ r≤2 ∧ -2≤c ∧ c≤2 ∧ -2≤r-dn ∧ r-dn≤2 ∧ -2≤c-dn ∧ c-dn≤2) :
    valid h (fine n h p.1 p.2) r c dn ↔
      0 ≤ (p.1.val:Int)+r ∧ (p.1.val:Int)+r < m ∧ 0 ≤ (p.2.val:Int)+c ∧ (p.2.val:Int)+c < m := by
  have ax (z : Fin n) (u : Int) (b : -2≤u ∧ u≤2 ∧ -2≤u-dn ∧ u-dn≤2) :
      validAxis h (axis n h z) u dn ↔ 0 ≤ (z.val:Int)+u ∧ (z.val:Int)+u < m := by
    have := z.isLt
    unfold validAxis axis; simp only [decide_eq_true_eq]; split_ifs <;> omega
  simp only [valid,Bool.and_eq_true,fine,List.getElem!_cons_zero,List.getElem!_cons_succ,
    ax _ r (by omega),ax _ c (by omega),and_assoc]
theorem port_some_small [NeZero n] (p q : Board n) (g : Fin 8) (d : Fin 4) {h : Nat}
    (big : 20≤n) (H : h=7 ∨ h=8) (res : (n+h)%3=0) (adj : shift p d=some q) :
    port h (fineViews h p g) (dirView g d)=some
      (if (dirView g d).val<2 then eventKey (coarse (small n g p)) (coarse (small n g q)) (dirView g d).val
       else eventKey (coarse (small n g q)) (coarse (small n g p)) ((dirView g d).val-2)) := by
  have a := (shift_iff _ _ _).mp ((shift_turn g d p q).mpr adj)
  have b := deltas (dirView g d)
  have v := (valid_small (small n g p) (r:=dr (dirView g d)) (c:=dc (dirView g d)) H big (m:=n) (dn:=0) (by omega) (by omega)).2
    (by have := (small n g q).1.isLt; have := (small n g q).2.isLt; omega)
  unfold port fineViews; rw [if_pos v]
  rw [moved_small _ (small n g p) H res big (by omega) (by omega) (by omega) (by decide),
      moved_small _ (small n g q) H res big a.1 a.2 (by omega) (by omega)]
theorem port_none_small [NeZero n] (p : Board n) (g : Fin 8) (d : Fin 4) {h : Nat}
    (big : 20≤n) (H : h=7 ∨ h=8) (adj : shift p d=none) :
    port h (fineViews h p g) (dirView g d)=none := by
  unfold port; apply if_neg; intro v
  have b := deltas (dirView g d)
  have a := (valid_small (small n g p) H big (m:=n) (dn:=0) (by omega) (by omega)).mp v
  let t : Board n := (⟨_,show ((↑(small n g p).1.val:Int)+dr (dirView g d)).toNat<n by omega⟩,
                      ⟨_,show ((↑(small n g p).2.val:Int)+dc (dirView g d)).toNat<n by omega⟩)
  let q := small n (invers g) t
  have inv : small n g q=t := by
    have eq : ∀ g, invers (invers g)=g := by decide
    simpa only [q,eq] using inverse (invers g) t
  have ex := (shift_turn g d p q).mp ((shift_iff _ _ _).mpr (by rw [inv]; dsimp [t]; constructor <;> omega))
  rw [adj] at ex; contradiction

end GridGraphs.NoPitch.FiniteRows
