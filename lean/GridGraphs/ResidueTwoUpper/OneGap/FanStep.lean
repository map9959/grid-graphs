import GridGraphs.ResidueTwoUpper.OneGap.FanSlabChart
import GridGraphs.ResidueTwoUpper.OneGap.FanSlab

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
open ResidueZero Stencil L7

def collapse (a b c j : Nat) :=
  if j<24 then j else if j<27+3*a then 24+(j-24)%3 else
  if j<81+3*a then j-3*a else if j<84+3*a+3*b then 81+(j-81-3*a)%3 else
  if j<144+3*a+3*b then j-3*a-3*b else if j<147+3*a+3*b+3*c then 144+(j-144-3*a-3*b)%3 else j-3*a-3*b-3*c
private theorem collapsed (a b c j : Nat) : follows (collapse a b c j) (collapse a b c (j+1)) := by
  unfold collapse follows starts; split_ifs <;> simp <;> omega

def bits (f : Fin 9 → Bool) := ((List.finRange 9).map fun q => (f q).toNat <<< q.val).sum
theorem unpack : ∀ f : Fin 9 → Bool, bits f<512 ∧ ∀ q : Fin 9, lane (bits f) q=(f q).toNat := by native_decide
private theorem shifts : ∀ (a b : Fin 512) (d : Bool),
    (∀ t : Fin 6, lane a (if d then 3+t.val else 3*(t.val/2)+t.val%2+1)=
      lane b (if d then t.val else 3*(t.val/2)+t.val%2)) →
    ov (if d then 1 else 0) a=ov (if d then 3 else 2) b := by native_decide

def square {n} (F : Finset (GridVertex n n)) (w : View) (r c : Nat) := bits fun q =>
  marked F (L7.view w n (r+q.val/3:Nat) (c+q.val%3:Nat))
theorem square_eq {n} (F : Finset (GridVertex n n)) (w : View) (r c : Nat) (a : origins n)
    (ha : coord a=L7.view w ((n:Int)-2) r c) : square F w r c=encode (maskAt F a) w := by
  have eq (q : Fin 9) : bit (maskAt F a) (posIdx (L7.view w 3 (q.val/3:Nat) (q.val%3:Nat))) =
      (marked F (L7.view w n (r+q.val/3:Nat) (c+q.val%3:Nat))).toNat := by
    let off := L7.view w 3 (q.val/3:Nat) (q.val%3:Nat)
    have ho : inside 3 off := inside_view (n:=3) w (by have := q.isLt; omega) (by omega)
    let t : Fin 9 := ⟨posIdx off,by simp [inside] at ho; unfold posIdx; omega⟩
    have B := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) t
    change bit (maskAt F a) t=(marked F (coord a+offset t)).toNat at B
    have O : offset t=off := by simp [inside] at ho; ext <;> simp [t,offset,posIdx] <;> omega
    rw [ha,O] at B; apply B.trans; congr 2
    cases w with | mk x y s => cases s <;> cases x <;> cases y <;> ext <;> simp [off,L7.view,reflect] <;> ring
  unfold square bits encode; simp_rw [eq]

theorem square_meet {n} (F : Finset (GridVertex n n)) (w : View) (r c : Nat) (d : Bool) :
    let a := square F w r c; let b := square F w (r+d.toNat) (c+(!d).toNat)
    ov (if d then 1 else 0) a=ov (if d then 3 else 2) b := by
  dsimp only
  apply shifts ⟨square F w r c,(unpack _).1⟩ ⟨square F w (r+d.toNat) (c+(!d).toNat),(unpack _).1⟩ d
  intro t
  let i : Fin 9 := ⟨if d then 3+t.val else 3*(t.val/2)+t.val%2+1,by have := t.isLt; split <;> omega⟩
  let k : Fin 9 := ⟨if d then t.val else 3*(t.val/2)+t.val%2,by have := t.isLt; split <;> omega⟩
  change lane (square F w r c) i=lane (square F w _ _) k
  unfold square; rw [(unpack _).2 i,(unpack _).2 k]; cases d <;> fin_cases t <;> dsimp [i,k] <;> congr 3 <;> omega

set_option maxHeartbeats 1500000 in
/-- Complete odd-fan (3,-6,3) step for two physically planted rows.
The pads x,y,z independently repeat entire tiles inside the three runs;
the 15-row slab uses true west/east fringe types. -/
theorem physical_step (u top x y z : Nat) (width : 11+14*u=57+x+y+z)
    (lo : 6≤top) (hi : top+19≤33+42*u) (ph : top%3=1)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p, P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (w : View)
    (stars : ∀ r<13, ∀ c≤30+42*u, ∀ p, coord p=L7.view w (35+42*(u:Int)) (top+r+1:Nat) (c+2:Nat) → starSlack F P p=0)
    (seed : ∀ r<6, ∀ c<33+42*u, (marked F (L7.view w (35+42*u:Nat) (top+r:Nat) (1+c:Nat))).toNat=
      lane (fan (r/3) (collapse x y z c/3)) (3*(c%3)+r%3)) :
    ∀ k<11+14*u, square F w (top+6) (1+3*k)=transpose (fan 2 (collapse x y z (3*k)/3)) := by
  let last := 30+42*u
  let C := collapse x y z
  let M (r c : Nat) := square F w (top+r) (1+c)
  have ct (c : Nat) (hc : c≤last) : C c<169 ∧ tag (C c)=realTag u c := by
    unfold C collapse tag realTag last at *; split_ifs <;> omega
  have followsWord : ∀ a b c : Fin 171, follows a b → follows b c → ∀ y : Fin 2,
      fan y (b.val/3)=fan y ((a.val+1)/3) ∧ fan y (c.val/3)=fan y ((a.val+2)/3) := by native_decide
  have mid (c k y : Nat) (hc : c≤last) (hk : k≤2) (hy : y<2) :
      fan y (C (c+k)/3)=fan y ((C c+k)/3) := by
    have bound (e : Nat) (he : e≤last+2) : C e<171 := by dsimp [C,collapse,last] at *; split_ifs <;> omega
    have hh := followsWord ⟨_,bound c (by omega)⟩ ⟨_,bound (c+1) (by omega)⟩ ⟨_,bound (c+2) (by omega)⟩
      (collapsed ..) (collapsed ..) ⟨y,hy⟩
    interval_cases k <;> first | rfl | exact hh.1 | exact hh.2
  have init (r : Nat) (hr : r<13) (c : Nat) (hc : c≤last) : M r c∈FanSlab.get base r (C c) := by
    have fj := (ct c hc).1
    let a := onSite (s:=35+42*u-2) (L7.view w (33+42*(u:Int)) (top+r:Nat) (c+1:Nat)) (by
      rw [show 35+42*u-2=33+42*u by omega]; exact_mod_cast inside_view (n:=33+42*u) w (by omega : top+r<_) (by dsimp [last] at hc; omega : c+1<_))
    have ha : coord a=L7.view w (33+42*(u:Int)) (top+r:Nat) (c+1:Nat) := coord_onSite ..
    let p := onSite (s:=35+42*u) (L7.view w (35+42*(u:Int)) (top+r+1:Nat) (c+2:Nat)) (by
      exact_mod_cast inside_view (n:=35+42*u) w (by omega : top+r+1<_) (by dsimp [last] at hc; omega : c+2<_))
    have hp : coord p=L7.view w (35+42*(u:Int)) (top+r+1:Nat) (c+2:Nat) := coord_onSite ..
    have rule := mask_rule u top r c lo hi ph hr hc F acy P step w a ha p (by
      rw [hp,ha,show (33+42*(u:Int))=35+42*(u:Int)-2 by ring,view_center]; push_cast; rfl) (clean a) (stars r hr c hc p hp)
    have e : M r c=encode (maskAt F a) w := square_eq F w _ _ a (by rw [ha]; push_cast; congr 1 <;> ring)
    apply base_mem (m:=M r c) hr fj (unpack _).1
    · unfold allowed; rw [(ct c hc).2,e]; exact rule
    · apply List.all_eq_true.mpr; intro k h; have h9 := List.mem_range.mp h
      let q : Fin 9 := ⟨k,h9⟩
      by_cases bd : 6≤r+k/3
      · simp [bd]
      apply Bool.or_eq_true_iff.mpr; right; apply beq_iff_eq.mpr
      change lane (square F w (top+r) (1+c)) q=_
      unfold square; rw [(unpack _).2 q]
      have E := seed (r+k/3) (by omega) (c+k%3) (by dsimp [last] at hc; omega)
      dsimp only [q]; simp only [Nat.add_assoc]; rw [E,mid c (k%3) _ hc (by omega) (by omega)]
      have ph' : c%3=C c%3 := by unfold C collapse; split_ifs <;> omega
      congr 1 <;> omega
  let T : Trace := {
    last := last
    column := C
    M := M
    lo := by simp [C,collapse]
    hi := by dsimp [C,collapse,last]; split_ifs <;> omega
    bound := fun c hc => (ct c hc).1
    progress := fun j _ => collapsed ..
    init := init
    down := fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (top+r) (1+c) true
    right := fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (top+r) (1+c) false }
  intro k hk
  have cj : 3*k≤last := by dsimp [last]; omega
  have mult : C (3*k)%3=0 := by dsimp [C,collapse]; split_ifs <;> omega
  exact third_row T (C (3*k)/3) (3*k) (by have := (ct _ cj).1; omega) cj (by change C (3*k)=_; omega)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
