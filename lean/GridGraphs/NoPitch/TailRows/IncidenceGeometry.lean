import GridGraphs.NoPitch.TailRows.OverlapCensus
import GridGraphs.NoPitch.Budget.StarPatch19

namespace GridGraphs.NoPitch.TailRows.Incidence
open PitchCut Keys LocalBoard19 Finset

abbrev Board (n : Nat) := Fin n × Fin n
def dr (d : Fin 4) : Int := if d.val=1 then 1 else if d.val=3 then -1 else 0
def dc (d : Fin 4) : Int := if d.val=0 then 1 else if d.val=2 then -1 else 0
def shift {n} (p : Board n) (d : Fin 4) : Option (Board n) :=
  let r := (p.1.val:Int)+dr d
  let c := (p.2.val:Int)+dc d
  if h : 0≤r ∧ 0≤c ∧ r.toNat<n ∧ c.toNat<n then some (⟨_,h.2.2.1⟩,⟨_,h.2.2.2⟩) else none
theorem shift_iff {n} (p q : Board n) (d : Fin 4) :
    shift p d=some q ↔ (q.1.val:Int)=p.1.val+dr d ∧ (q.2.val:Int)=p.2.val+dc d := by
  unfold shift; simp only [Option.dite_none_right_eq_some,Option.some.injEq]
  constructor
  · rintro ⟨h,rfl⟩; simp [Int.toNat_of_nonneg h.1,Int.toNat_of_nonneg h.2.1]
  · rintro ⟨a,b⟩
    refine ⟨by simp only [←a,←b,Int.natCast_nonneg,Int.toNat_natCast,Fin.is_lt,and_self],?_⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
theorem shift_probe {k} (p : Site k) (d : Fin 4) : shift p d=probe p d.val := by
  fin_cases d <;> rfl
theorem geom {n} (p q : Board n) (d : Fin 4) (h : shift p d=some q) :
    shift q (opp d)=some p ∧ ∀ e, shift p e=some q → e=d := by
  rw [shift_iff] at h ⊢
  constructor
  · fin_cases d <;> norm_num [dr,dc,opp,Fin.add_def] at h ⊢ <;> omega
  · intro e he; rw [shift_iff] at he
    fin_cases d <;> fin_cases e <;> norm_num [dr,dc] at he h ⊢ <;> omega

def reverse {n} (p : Board n × Fin 4) := match shift p.1 p.2 with
  | none => p | some q => (q,opp p.2)
theorem cancel {n} (amt : Board n × Fin 4 → Int)
    (outside : ∀ p d, shift p d=none → amt (p,d)=0)
    (opposite : ∀ p q d, shift p d=some q → amt (p,d)= -amt (q,opp d)) :
    ∑ p, amt p=0 := by
  have oo : ∀ d, opp (opp d)=d := by decide
  have inv : Function.Involutive (@reverse n) := by
    rintro ⟨p,d⟩; cases h : shift p d with
    | none => simp [reverse,h]
    | some q => simp [reverse,h,(geom _ _ _ h).1,oo]
  let e : Board n × Fin 4 ≃ _ := ⟨reverse,reverse,inv,inv⟩
  have anti (p : Board n × Fin 4) : amt p= -amt (reverse p) := by
    rcases p with ⟨p,d⟩; cases h : shift p d with
    | none => simp [reverse,h,outside _ _ h]
    | some q => simpa [reverse,h] using opposite _ _ _ h
  have z := sum_congr (s₁:=univ) rfl (fun p _ => anti p)
  have bij : (∑ p, amt (reverse p))=∑ p, amt p := e.sum_comp amt
  rw [sum_neg_distrib,bij] at z
  change (∑ p, amt p)= -(∑ p, amt p) at z
  omega

/-- Encode a coarse position at a bounded displacement using only the
fine centre label. `dn` changes board size (patch origin vs star). -/
def axisMove (h a : Nat) (u dn : Int) : Nat :=
  let n : Int := 57-h
  let t : Int := if a<h then a else if a<h+3 then a+12 else n+a-(2*h+3:Int)
  if t+u<4 then (t+u).toNat else if n+dn-4≤t+u then (11+t+u-(n+dn)).toNat
    else (4+(t+u-4)%3).toNat
def cl4 (x : Int) := (max (-4) (min 4 x)+4).toNat
def moved (h : Nat) (v : List Nat) (r c dn : Int) :=
  [axisMove h v[0]! r dn,axisMove h v[1]! c dn,
    cl4 ((v[2]!:Int)-9+r-c),cl4 ((v[3]!:Int)-9+r+c-dn)]

theorem moved_eq {n m h} (p : Board n) (q : Board m) {r c dn : Int}
    (H : h=7 ∨ h=8) (res : (n+h)%3=0) (big : 40≤n) (R : (q.1.val:Int)=p.1.val+r)
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
end GridGraphs.NoPitch.TailRows.Incidence
