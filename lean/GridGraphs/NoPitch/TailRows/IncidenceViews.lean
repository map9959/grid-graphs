import GridGraphs.NoPitch.TailRows.IncidenceChecks

namespace GridGraphs.NoPitch.TailRows.Incidence
open PitchCut Keys LocalBoard19 Finset
variable {n k : Nat}
theorem pos {n} [NeZero n] (g : Fin 8) (p : Board n) :
    ((small n g p).1.val,(small n g p).2.val)=transform g n p.1 p.2 := by
  have := p.1.isLt; have := p.2.isLt; have := Nat.pos_of_ne_zero (NeZero.ne n)
  fin_cases g <;> norm_num [small,transform,Fin.ofNat,Prod.ext_iff] <;>
    simp (disch := omega) only [Nat.mod_eq_of_lt,and_true,true_and]

def fineViews {n} [NeZero n] (h : Nat) (p : Board n) (g : Fin 8) :=
  fine n h (small n g p).1 (small n g p).2
theorem patch_views [NeZero (N k-2)] (p : PatchPos k) : patchFine p=fineViews 7 p := by
  funext g; unfold fineViews patchFine; rw [←pos g p]

theorem inverse [NeZero n] (g : Fin 8) (p : Board n) : small n (invers g) (small n g p)=p := by
  have := p.1.isLt; have := p.2.isLt; have := Nat.pos_of_ne_zero (NeZero.ne n)
  fin_cases g <;> norm_num [small,invers,transform,Fin.ofNat,Prod.ext_iff,Fin.ext_iff] <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt,and_true,true_and]) <;> omega
theorem shift_turn [NeZero n] (g : Fin 8) (d : Fin 4) (p q : Board n) :
    shift (small n g p) (dirView g d)=some (small n g q) ↔ shift p d=some q := by
  rw [shift_iff,shift_iff]
  have a := pos g p; have b := pos g q
  have := p.1.isLt; have := p.2.isLt; have := q.1.isLt; have := q.2.isLt
  fin_cases g <;> fin_cases d <;> norm_num [dr,dc,dirView,direction,Fin.ofNat,transform,Prod.ext_iff] at a b ⊢ <;> omega

theorem valid_eq {n m h} (p : Board n) {r c dn : Int}
    (H : h=7 ∨ h=8) (big : 40≤n) (D : (m:Int)=n+dn)
    (bound : -2≤r ∧ r≤2 ∧ -2≤c ∧ c≤2 ∧ -2≤r-dn ∧ r-dn≤2 ∧ -2≤c-dn ∧ c-dn≤2) :
    valid h (fine n h p.1 p.2) r c dn ↔
      0 ≤ (p.1.val:Int)+r ∧ (p.1.val:Int)+r < m ∧ 0 ≤ (p.2.val:Int)+c ∧ (p.2.val:Int)+c < m := by
  have ax (z : Fin n) (u : Int) (b : -2≤u ∧ u≤2 ∧ -2≤u-dn ∧ u-dn≤2) :
      validAxis h (axis n h z) u dn ↔ 0 ≤ (z.val:Int)+u ∧ (z.val:Int)+u < m := by
    have := z.isLt
    unfold validAxis axis; simp only [decide_eq_true_eq]; split_ifs <;> omega
  simp only [valid,Bool.and_eq_true,fine,List.getElem!_cons_zero,List.getElem!_cons_succ,
    ax _ r (by omega),ax _ c (by omega),and_assoc]
theorem dirReverse : ∀ (g : Fin 8) (d : Fin 4), (dirView g (opp d)).val=((dirView g d).val+2)%4 := by decide
theorem deltas (d : Fin 4) : -1≤dr d ∧ dr d≤1 ∧ -1≤dc d ∧ dc d≤1 := by
  fin_cases d <;> decide
theorem port_some [NeZero n] (p q : Board n) (g : Fin 8) (d : Fin 4) {h : Nat}
    (big : 40≤n) (H : h=7 ∨ h=8) (res : (n+h)%3=0) (adj : shift p d=some q) :
    port h (fineViews h p g) (dirView g d)=some
      (if (dirView g d).val<2 then eventKey (coarse (small n g p)) (coarse (small n g q)) (dirView g d).val
       else eventKey (coarse (small n g q)) (coarse (small n g p)) ((dirView g d).val-2)) := by
  have a := (shift_iff _ _ _).mp ((shift_turn g d p q).mpr adj)
  have b := deltas (dirView g d)
  have v := (valid_eq (small n g p) (r:=dr (dirView g d)) (c:=dc (dirView g d)) H big (m:=n) (dn:=0) (by omega) (by omega)).2
    (by have := (small n g q).1.isLt; have := (small n g q).2.isLt; omega)
  unfold port fineViews; rw [if_pos v]
  rw [moved_eq _ (small n g p) H res big (by omega) (by omega) (by omega) (by decide),
      moved_eq _ (small n g q) H res big a.1 a.2 (by omega) (by omega)]
theorem port_none [NeZero n] (p : Board n) (g : Fin 8) (d : Fin 4) {h : Nat}
    (big : 40≤n) (H : h=7 ∨ h=8) (adj : shift p d=none) :
    port h (fineViews h p g) (dirView g d)=none := by
  unfold port; apply if_neg; intro v
  have b := deltas (dirView g d)
  have a := (valid_eq (small n g p) H big (m:=n) (dn:=0) (by omega) (by omega)).mp v
  let t : Board n := (⟨_,show ((↑(small n g p).1.val:Int)+dr (dirView g d)).toNat<n by omega⟩,
                      ⟨_,show ((↑(small n g p).2.val:Int)+dc (dirView g d)).toNat<n by omega⟩)
  let q := small n (invers g) t
  have inv : small n g q=t := by
    have eq : ∀ g, invers (invers g)=g := by decide
    simpa only [q,eq] using inverse (invers g) t
  have ex := (shift_turn g d p q).mp ((shift_iff _ _ _).mpr (by rw [inv]; dsimp [t]; constructor <;> omega))
  rw [adj] at ex; contradiction
end GridGraphs.NoPitch.TailRows.Incidence
