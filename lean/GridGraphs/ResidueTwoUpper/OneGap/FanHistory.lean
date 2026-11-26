import GridGraphs.ResidueTwoUpper.OneGap.FanBootScore

local macro "lin" : tactic => `(tactic| first | omega | (simp only [abs_eq_max_neg] at * <;> omega))

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed BoundarySix.Connected

/-- North row before the shrinking word starts. All coordinates in `Read`
are local offsets from the interior origin (1,1). -/
def seedWord (q i : Nat) := if i=0 then 16 else if i+1<q then 48 else if i<q then 16 else if i=q then 4 else 6
def history (q j i : Nat) := if j=0 then seedWord q i else actual q j i
def Read (n q j : Nat) (F : Finset (GridVertex n n)) (w : View) := ∀ i a b : Nat,
    1+3*i+a<n-1 → a<3 → b<3 → (marked F (L7.view w n (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat=lane (history q j i) (3*a+b)

set_option maxHeartbeats 700000 in
theorem right_bits (q j i a b : Nat) (ha : a<3) (hb : b<3) (lo : 1+3*j≤ i) (middle : 6*j+2≤q)
    (m : lane (history q j i) (3*a+b)=1) : NorthFanLines.mark q i j a b := by
  unfold history at m; split at m
  · subst j; unfold seedWord at m; split_ifs at m <;> interval_cases a <;> interval_cases b <;>
      norm_num [lane] at m <;> unfold NorthFanLines.mark <;> omega
  · let d := (q:Int)-i-3*j
    have rule : actual q j i=(if 2≤d then 56 else if d=1 then 24 else if d=0 then 12 else if d= -1 then 6 else 7) := by
      dsimp only [actual,word,d]; split_ifs <;> first | rfl | omega | rw [show i-(3*j-2+3+(q-6*j-2))=0 by omega] | rw [show i-(3*j-2+3+(q-6*j-2))=1 by omega] | rw [show i-(3*j-2+3+(q-6*j-2))=2 by omega]
      all_goals decide
    rw [rule] at m; dsimp only [d] at m; split_ifs at m <;> interval_cases a <;> interval_cases b <;>
      norm_num [lane] at m <;> unfold NorthFanLines.mark <;> omega

private theorem view_coords {n} (w : View) (p : GridVertex n n) :
    L7.view w n (coordinates w p).1 (coordinates w p).2=coord p := by
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> ext <;> simp [coordinates,L7.view,reflect]
private theorem inside_coords {n} (w : View) (p : GridVertex n n) : inside n (coordinates w p) := by
  have a := p.1.isLt; have b := p.2.isLt
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [inside,coordinates,reflect,coord] <;> omega

/-- The cut is the first row of tile Y+1. The next-row test of `sealed`
is read from the same final tile, not inferred from the upper component. -/
theorem dangling_through_cut (n q y t : Nat) (fits : 3*q+8≤n)
    (left : 2≤t) (born : q+2≤t+3*y) (right : t≤q) (F : Finset (GridVertex n n)) (w : View)
    (read : ∀ j≤y, ∀ i a b : Nat, 3*j+b≤3*y+1 → q≤t+3*j+2 → i≤t → t ≤ i+1 → 1+3*i+a<n-1 → a<3 → b<3 →
      marked F (L7.view w n (1+3*j+b:Nat) (1+3*i+a:Nat))=true → NorthFanLines.mark q i j a b) :
    let d : Int := 1+3*(y:Int); let c : Int := 1+3*(t:Int); let birth : Int := (q:Int)-t+3
    clear F w birth d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c := by
  dsimp only
  have word' (v) (hv : v∈F) (rows : (q:Int)-t+1≤(coordinates w v).1 ∧ (coordinates w v).1≤2+3*(y:Int))
      (cols : |(coordinates w v).2-(1+3*(t:Int))|≤2) : ∃ i j a b : Int,
      (coordinates w v)=(1+3*j+b,1+3*i+a) ∧ NorthFanLines.mark q i j a b := by
    let R := ((coordinates w v).1-1).toNat; let C := ((coordinates w v).2-1).toNat
    have rr : (R:Int)=(coordinates w v).1-1 := by dsimp [R]; lin
    have cc : (C:Int)=(coordinates w v).2-1 := by dsimp [C]; lin
    have pos : coord v=L7.view w n (1+3*(R/3)+R%3:Nat) (1+3*(C/3)+C%3:Nat) := by
      rw [←view_coords w v]; congr 1 <;> lin
    have yes := marked_at F v; rw [decide_eq_true hv, pos] at yes
    have eq := read (R/3) (by lin) (C/3) (C%3) (R%3) (by lin) (by lin) (by lin) (by lin) (by lin) (by lin) (by lin)
    exact ⟨((C/3:Nat):Int),((R/3:Nat):Int),((C%3:Nat):Int),((R%3:Nat):Int),Prod.ext (by push_cast; lin) (by push_cast; lin),eq yes⟩
  constructor
  · rw [show 1+3*(t:Int)=3*(t:Int)+1 by ring]; apply fan_clear F w q t _ (by lin)
    intro v hv le near; obtain ⟨z,az,zd,h⟩ := near
    exact word' v hv ⟨by lin,by lin⟩ (by lin)
  · intro v hv row col
    obtain ⟨i,j,a,b,E,m⟩ := word' v hv ⟨by lin,by lin⟩ (by lin)
    have near : |3*i+a-3*(t:Int)|+|3*j+b-(1+3*(y:Int))|≤2 := by rw [E] at row col; dsimp at row col; lin
    have yes := NorthFanLines.isolated q t i j a b (1+3*(y:Int)) (by lin) (by lin) m near
    rw [E]; dsimp; lin

theorem dangling_of_marks (n q y t : Nat) (fits : 3*q+8≤n)
    (left : 2≤t) (born : q+2≤t+3*y) (right : t≤q) (F : Finset (GridVertex n n)) (w : View)
    (read : ∀ j≤y, ∀ i a b : Nat, q≤t+3*j+2 → i≤t → t ≤ i+1 → 1+3*i+a<n-1 → a<3 → b<3 →
      marked F (L7.view w n (1+3*j+b:Nat) (1+3*i+a:Nat))=true → NorthFanLines.mark q i j a b) :
    let d : Int := 1+3*(y:Int); let c : Int := 1+3*(t:Int); let birth : Int := (q:Int)-t+3
    clear F w birth d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c :=
  dangling_through_cut n q y t fits left born right F w (fun j hj i a b _ => read j hj i a b)

theorem dangling_after_birth (n q y t : Nat) (hyq : 6*y+2≤q) (fits : 3*q+8≤n)
    (left : 3*y+2≤t) (born : q+2≤t+3*y) (right : t≤q) (F : Finset (GridVertex n n)) (w : View)
    (read : ∀ j≤y, ∀ i a b : Nat, q≤t+3*j+2 → i≤t → t ≤ i+1 → 1+3*i+a<n-1 → a<3 → b<3 →
      (marked F (L7.view w n (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat=lane (history q j i) (3*a+b)) :
    let d : Int := 1+3*(y:Int); let c : Int := 1+3*(t:Int); let birth : Int := (q:Int)-t+3
    clear F w birth d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c := by
  apply dangling_of_marks n q y t fits (by omega) born right
  intro j hj i a b near it ti fit al bl m
  have eq := read j hj i a b near it ti fit al bl
  rw [m] at eq
  exact right_bits q j i a b al bl (by omega) (by omega) eq.symm

theorem dangling_in_collar (n q y t : Nat) (hyq : 6*y+2≤q) (fits : 3*q+8≤n)
    (left : 3*y+2≤t) (born : q+2≤t+3*y) (right : t≤q) (F : Finset (GridVertex n n)) (w : View)
    (read : ∀ j≤y, ∀ i a b : Nat, i≤t → t ≤ i+1 → 1+3*i+a<n-1 → a<3 → b<3 →
      (marked F (L7.view w n (1+3*j+b:Nat) (1+3*i+a:Nat))).toNat=lane (history q j i) (3*a+b)) :
    let d : Int := 1+3*(y:Int); let c : Int := 1+3*(t:Int); let birth : Int := (q:Int)-t+3
    clear F w birth d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c :=
  dangling_after_birth n q y t hyq fits left born right F w (fun j hj i a b _ => read j hj i a b)

theorem dangling_at_handoff (n q Y t : Nat) (hy : 6≤Y) (hyq : 6*Y+15≤q) (fits : 3*q+8≤n)
    (left : q-3*Y+3≤t) (right : t≤q) (F : Finset (GridVertex n n)) (w : View)
    (read : ∀ j≤Y+1, Read n q j F w) :
    let d : Int := 1+3*((Y:Int)+1); let c : Int := 1+3*(t:Int); let birth : Int := (q:Int)-t+3
    clear F w birth d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c := by
  simpa only [Nat.cast_add,Nat.cast_one] using dangling_in_collar n q (Y+1) t (by omega) fits
    (by omega) (by omega) right F w (fun j hj i a b _ _ => read j hj i a b)

/-- A window outputs full row-major masks 73 on its plateau (the
transposed speed word 7). These two neighboring tiles supply the whole
collar, including the next-row contact, even at the true east end. -/
def Plateau {n} (F : Finset (GridVertex n n)) (w : View) (y endY f k : Nat) := ∀ j, y≤j → j≤endY → ∀ i, f≤ i → i< k → square F w (1+3*j) (1+3*i)=73
theorem plateau_bit {n} {F : Finset (GridVertex n n)} {w : View} {r c : Nat}
    (m : square F w r c=73) (a b : Fin 3) : (marked F (L7.view w n (r+b.val:Nat) (c+a.val:Nat))).toNat=(decide (a.val=0)).toNat := by
  let t : Fin 9 := ⟨3*b.val+a.val,by lin⟩
  have e := (unpack (fun s : Fin 9 => marked F (L7.view w n (r+s.val/3:Nat) (c+s.val%3:Nat)))).2 t
  change lane (square F w r c) t=_ at e; rw [m] at e
  have tab : ∀ a b : Fin 3, lane 73 (3*b.val+a.val)=(decide (a.val=0)).toNat := by decide
  simpa only [t,show (3*b.val+a.val)/3=b.val by lin,show (3*b.val+a.val)%3=a.val by lin,tab] using e.symm

theorem plateau_transport {n} (F : Finset (GridVertex n n)) (w : View) (y e f k t : Nat) (le : y≤e) (lt : f<t ∧ t<k)
    (pl : Plateau F w y e f k) (a : Int) (ad : a≤1+3*(y:Int)) (old : clear F w a (1+3*(y:Int)) (1+3*(t:Int))) :
    clear F w a (1+3*(e:Int)) (1+3*(t:Int)) ∧ ∀ v∈F, (coordinates w v).1=2+3*(e:Int) →
      |(coordinates w v).2-(1+3*(t:Int))|≤1 → (coordinates w v).2=1+3*(t:Int) := by
  have slab (v) (hv : v∈F) (row : 1+3*(y:Int)≤(coordinates w v).1 ∧ (coordinates w v).1≤2+3*(e:Int))
      (col : |(coordinates w v).2-(1+3*(t:Int))|≤2) : (coordinates w v).2=1+3*(t:Int) := by
    let R := ((coordinates w v).1-1).toNat; let C := ((coordinates w v).2-1).toNat
    have rr : (R:Int)=(coordinates w v).1-1 := by dsimp [R]; lin
    have cc : (C:Int)=(coordinates w v).2-1 := by dsimp [C]; lin
    have z := plateau_bit (pl (R/3) (by lin) (by lin) (C/3) (by lin) (by lin)) ⟨C%3,by lin⟩ ⟨R%3,by lin⟩
    have pos : L7.view w n (1+3*(R/3)+R%3:Nat) (1+3*(C/3)+C%3:Nat)=coord v := by rw [←view_coords w v]; congr 1 <;> lin
    rw [pos,marked_at,decide_eq_true hv] at z
    by_contra ne; have e : C%3≠0 := by lin
    simp [e] at z
  exact ⟨extend_clear F w _ _ _ _ ad (by lin) old (fun v hv l h c => slab v hv ⟨by lin,by lin⟩ c),
    fun v hv h c => slab v hv ⟨by lin,by lin⟩ (by lin)⟩

theorem plateau_carry {n} (F : Finset (GridVertex n n)) (w : View) (y e f k t : Nat) (le : y≤e) (col : f≤t ∧ t<k)
    (pl : Plateau F w y e f k) (hc : 0<1+3*t ∧ 1+3*t+1<n) (hd : 1+3*e+1<n) (src : Crop n)
    (path : ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (inner w (1+3*y) (1+3*t) (by lin) hc)) :
    ((Bonds F).induce {p | ¬IsGridBoundary p}).Reachable src (inner w (1+3*e) (1+3*t) (by lin) hc) := by
  apply carry F w _ _ _ hc (by lin) (by lin) hd src path
  intro r hr he; apply Bool.or_eq_true_iff.mpr; left
  have z := plateau_bit (pl ((r-1)/3) (by lin) (by lin) t col.1 col.2) 0 ⟨(r-1)%3,by lin⟩
  change (marked F (L7.view w _ (1+3*((r-1)/3)+(r-1)%3:Nat) (1+3*t+0:Nat))).toNat=1 at z
  rw [show 1+3*((r-1)/3)+(r-1)%3=r by lin] at z; simpa using z
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
