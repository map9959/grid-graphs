import GridGraphs.ResidueTwoUpper.OneGap.FanBootGeo
import GridGraphs.ResidueTwoUpper.OneGap.FanBootScan
import GridGraphs.ResidueTwoUpper.OneGap.FanRootTransport

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSweep FanSeed BoundarySix.Connected

def foldCol (x z c : Nat) :=
  if c<81 then c else if c<84+3*x then 81+(c-81)%3 else
  if c<180+3*x then c-3*x else if c<183+3*x+3*z then 180+(c-180-3*x)%3 else c-3*x-3*z
private theorem adjacent' (h x z c : Nat) (hz : h=8 ∨ z=0) :
    foldCol x z (c+1)∈pred (box h) false (foldCol x z c) ∧ foldCol x z c∈pred (box h) true (foldCol x z (c+1)) := by
  have H : foldCol x z (c+1)=foldCol x z c+1 ∨ (foldCol x z c=83 ∧ foldCol x z (c+1)=81) ∨
      (h=8 ∧ foldCol x z c=182 ∧ foldCol x z (c+1)=180) := by unfold foldCol; split_ifs <;> omega
  rcases H with e|⟨a,b⟩|⟨rfl,a,b⟩
  · simp [pred,e]
  · simp [pred,box,a,b]; split <;> decide
  · simp [pred,box,a,b]

def Rows (u q : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) :=
  ∀ r<6, ∀ c<33+42*u, (marked F (L7.view w (35+42*u:Nat) (19+r:Nat) (1+c:Nat))).toNat=
    lane (fan (r/3) (collapse 0 (q-57) (11+14*u-q) c/3)) (3*(c%3)+r%3)

theorem tile_eq {u j : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) (hj : j<33+42*u) :
    tile F w 1 j=square F w 1 j := by
  let a := onSite (s:=35+42*u-2) (L7.view w (33+42*(u:Int)) 1 j) (by
    rw [show 35+42*u-2=33+42*u by omega]; exact_mod_cast inside_view (n:=33+42*u) (r:=1) w (by omega) hj)
  have h : coord a=L7.view w (33+42*(u:Int)) 1 j := coord_onSite ..
  rw [square_eq F w 1 j a (by rw [h]; push_cast; congr 1 <;> ring),window_encode u F w 1 j (by decide) a (by rw [h]; congr 1 <;> ring)]
  rfl

set_option maxHeartbeats 1200000 in
theorem with_boot_chart {goal : Prop} (u q : Nat) (lq : 57≤q) (hq : q+2≤11+14*u) (odd : q%2=1)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (w : View)
    (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (west : ∀ i<q, marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat)))
    (core : tile F w 1 (1+3*q)=64) (east : ∀ i, q< i → i<11+14*u → tile F w 1 (1+3*i)=72) (useChart : ∀ h x z, (h=2 ∨ h=4 ∨ h=6 ∨ h=8) → (h=8 ∨ z=0) →
      q=57+x ∧ 11+14*u=57+h+x+z → ∀ T : Path (box h), T.last=30+42*u → T.col=foldCol x z →
      T.M=(fun r c => square F w (1+r) (1+c)) → Kept T (FanBoot.base h) → goal) : goal := by
  let h := min 8 (11+14*u-q); let x := q-57; let z := 11+14*u-q-h
  have hh : h=2 ∨ h=4 ∨ h=6 ∨ h=8 := by dsimp [h]; omega
  have hz : h=8 ∨ z=0 := by dsimp [h,z]; omega
  have eqs : q=57+x ∧ 11+14*u=57+h+x+z := by dsimp [x,h,z]; omega
  let last := 30+42*u; let C := foldCol x z; let M (r c : Nat) := square F w (1+r) (1+c)
  have ct (c : Nat) (hc : c≤last) : C c≤(box h).cols ∧ colTag h (C c)=realTag u c := by
    dsimp only [C,colTag,box,last] at *; unfold foldCol realTag; split_ifs <;> omega
  have init (r c : Nat) (hr : r≤27) (hc : c≤last) : M r c∈cell (FanBoot.base h) r (C c) := by
    have cm := (ct c hc).1
    have bounds : M r c<512 := (unpack _).1
    have coin : C c=171 ↔ c=3*q := by unfold C foldCol; split_ifs <;> omega
    have phase : (C c)%3=c%3 := by unfold C foldCol; split_ifs <;> omega
    have perm : C c<171 ↔ c<3*q := by unfold C foldCol; split_ifs <;> omega
    have regular : (r==0 && C c==171) || accepts (rowTag r) (colTag h (C c)) (M r c) := by
      by_cases same : r=0 ∧ c=3*q
      · exact Bool.or_eq_true_iff.mpr (.inl (by simp [same.1,coin.mpr same.2]))
      apply Bool.or_eq_true_iff.mpr; right; rw [(ct c hc).2]
      apply accept_physical u r c (by omega) hr hc F acy P step w clean
      intro p hp; apply zero; rw [hp]; intro eq
      cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at eq <;> omega
    have st : startOK r (C c) (M r c) := by
      unfold startOK
      split
      swap
      · exact rfl
      rename_i A
      obtain ⟨rr,al⟩ := Bool.and_eq_true_iff.mp A
      have rr := beq_iff_eq.mp rr; subst r
      have al' := beq_iff_eq.mp al
      split
      · rename_i left
        have pos := west (c/3) (by omega)
        have bit4 := (unpack (fun q : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+q.val/3:Nat) (1+c+q.val%3:Nat)))).2 4
        apply beq_iff_eq.mpr; apply bit4.trans
        change (marked F (L7.view w _ 2 (1+c+1:Nat))).toNat=1
        rw [show 1+c+1=2+3*(c/3) by omega,pos]; rfl
      · have t := tile_eq F w (j:=1+c) (by dsimp [last] at hc; omega)
        apply beq_iff_eq.mpr; apply t.symm.trans
        split
        · rename_i H; simpa only [coin.mp H] using core
        · simpa only [show 1+3*(c/3)=1+c by omega] using east (c/3) (by omega) (by dsimp [last] at hc; omega)
    simp [cell,FanBoot.base,build,show r<(box h).rows+1 from Nat.lt_succ_of_le hr,show C c<(box h).cols+1 by omega,bounds,regular,st]
  let T : Path (box h) := {
    last := last
    col := C
    M := M
    start := by simp [C,foldCol]
    stop := by dsimp only [C,last,box]; unfold foldCol; split_ifs <;> omega
    bound := fun c hc => (ct c hc).1
    next := fun c _ => adjacent' h x z c hz
    across := fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) false
    down := fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+r) (1+c) true }
  exact useChart h x z hh hz eqs T rfl rfl rfl (fun r hr c hc => init r c hr hc)

set_option maxHeartbeats 1200000 in
theorem rows_from_teeth (u q : Nat) (lq : 57≤q) (hq : q+2≤11+14*u) (odd : q%2=1)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (w : View)
    (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (west : ∀ i<q, marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat)))
    (core : tile F w 1 (1+3*q)=64) (east : ∀ i, q< i → i<11+14*u → tile F w 1 (1+3*i)=72) : Rows u q F w := by
  apply with_boot_chart u q lq hq odd F acy P step clean w zero west core east
  intro h x z hh hz eqs T tlast tcol tmask init
  let C := foldCol x z; let last := 30+42*u
  have ct (c : Nat) (hc : c≤last) : C c≤(box h).cols := by unfold C; rw [←tcol]; exact T.bound c (by omega)
  intro r hr c hc
  let k := c/3; let y := r/3; let idx := C (3*k)/3
  have cj : 3*k≤last := by dsimp [last,k]; omega
  have aligned : C (3*k)=3*idx := by unfold idx C foldCol; split_ifs <;> omega
  have idxb : idx<57+h := by have := ct _ cj; dsimp [box] at this; omega
  have word := output h (by simp; omega) T init (3*k) y idx (by omega) (by dsimp [y]; omega) idxb (by rw [tcol]; exact aligned)
  rw [tmask] at word
  change square F w (1+(18+3*y)) (1+3*k)=_ at word
  let i : Fin 9 := ⟨3*(r%3)+c%3,by omega⟩
  have decode := (unpack (fun b : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+(18+3*y)+b.val/3:Nat) (1+3*k+b.val%3:Nat)))).2 i
  change lane (square F w _ _) i=_ at decode; rw [word] at decode
  have transpose_bit : ∀ m : Fin 512, ∀ i : Fin 9, lane (transpose m) i=lane m (3*(i.val%3)+i.val/3) := by native_decide
  have hy : y=0 ∨ y=1 := by dsimp [y]; omega
  have small : ∀ y : Fin 2, ∀ k : Fin 65, fan y k<512 := by native_decide
  have mb := small ⟨y,by omega⟩ ⟨idx,by omega⟩
  change fan y idx<512 at mb
  have bitEq := transpose_bit ⟨_,mb⟩ i
  change lane (transpose (fan y idx)) i=_ at bitEq
  rw [bitEq] at decode
  change lane (fan y idx) (3*(i.val%3)+i.val/3)=_ at decode
  have fw : fan y idx=fan y (collapse 0 x (h+z) c/3) := by
    have loc : (idx=collapse 0 x (h+z) c/3) ∨
        (idx≥41 ∧ collapse 0 x (h+z) c/3≥41) ∨
        (22≤ idx ∧ idx≤34 ∧ 22≤collapse 0 x (h+z) c/3 ∧ collapse 0 x (h+z) c/3≤34) := by
      unfold idx C foldCol collapse; dsimp only [k]; split_ifs <;> omega
    rcases loc with e|e|e
    · rw [e]
    all_goals rcases hy with h0|h0 <;> rw [h0] <;> dsimp only [fan] <;> split_ifs <;> first | rfl | omega
  rw [fw] at decode
  have R : 1+(18+3*y)+i.val/3=19+r := by dsimp [i,y]; omega
  have K : 1+3*k+i.val%3=1+c := by dsimp [i,k]; omega
  rw [R,K] at decode
  simpa only [show q-57=x by omega,show 11+14*u-q=h+z by omega,show 3*(i.val%3)+i.val/3=3*(c%3)+r%3 by dsimp [i]; omega] using decode.symm
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
