import GridGraphs.ResidueTwoUpper.OneGap.FanHaloPhysical
import GridGraphs.ResidueTwoUpper.OneGap.FanSeam
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
open L7 FanSlab FanSeed Port Halo ResidueZero Stencil

def marksAt {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (R C : Nat) : Marks := fun b a => bitAt F w ((R+b:Nat),(C+a:Nat))
def dirsAt {u} {F : Finset (GridVertex (N u) (N u))} (Q : Flow F) (w : View) (R C : Nat) : Arrows := fun b a => Fin.ofNat 4 (arrow Q.parent w ((R+b:Nat),(C+a:Nat)))
private theorem sq {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (R C r c : Nat) : bits (ink (marksAt F w R C) r c)=square F w (R+r) (C+c) := by unfold ink marksAt bitAt square; simp only [Nat.add_assoc]

/-- A translated rectangle of physical bits and compass arrows, with
independent marks at every site and no interior sinks. -/
theorem rect {u} (F : Finset (GridVertex (N u) (N u))) (Q : Flow F) (w : View) (price : Prices F w)
    (R C h w' : Nat) (rr : 8≤R ∧ R+h+6≤33+42*u) (cc : 8≤C ∧ C+w'+6≤33+42*u) :
    let M := marksAt F w R C; let A := dirsAt Q w R C
    (∀ r<h, ∀ c, c+1<w' → Across M A r c) ∧ (∀ r,r+1<h → ∀ c<w', Down M A r c) ∧
    (∀ r, r+2<h → ∀ c,c+2<w' → active (bits (ink M r c)) (A (r+1) (c+1)).val) := by
  let M := marksAt F w R C; let D (r c : Nat) := arrow Q.parent w ((R+r:Nat),(C+c:Nat)); let A := dirsAt Q w R C
  have bound (r c : Nat) (hr : r<h) (hc : c<w') : D r c<4 := dir_lt F w Q price _ _ (by omega) (by omega)
  have norm (r c : Nat) (hr : r<h) (hc : c<w') (d : Fin 4) : (A r c==d)=(D r c==d.val) := by simp only [A,D,dirsAt,beq_eq_decide,Fin.ext_iff,Fin.ofNat,Nat.mod_eq_of_lt (bound r c hr hc)]
  have H (r c : Nat) (hr : r<h) (hc : c+1<w') : Across M A r c := by
    have eq : shift ((R+r:Nat),(C+c:Nat)) 0=(((R+r:Nat):Int),((C+(c+1):Nat):Int)) := by ext <;> simp [shift]; ring
    have z := Camera.cross (w:=w) Q.step Q.covers 0 (p:=((R+r:Nat),(C+c:Nat))) (by dsimp [In,N]; omega) (by change In _ (shift _ 0); rw [eq]; dsimp [In,N]; omega)
    change Own (D r c==0) (arrow Q.parent w (shift ((R+r:Nat),(C+c:Nat)) 0)==2) (M r c) (bitAt F w (shift ((R+r:Nat),(C+c:Nat)) 0)) at z
    rw [eq] at z; unfold Across; rw [norm _ _ hr (by omega),norm _ _ hr hc]; exact z
  have V (r c : Nat) (hr : r+1<h) (hc : c<w') : Down M A r c := by
    have eq : shift ((R+r:Nat),(C+c:Nat)) 1=(((R+(r+1):Nat):Int),((C+c:Nat):Int)) := by ext <;> simp [shift]; ring
    have z := Camera.cross (w:=w) Q.step Q.covers 1 (p:=((R+r:Nat),(C+c:Nat))) (by dsimp [In,N]; omega) (by change In _ (shift _ 1); rw [eq]; dsimp [In,N]; omega)
    change Own (D r c==1) (arrow Q.parent w (shift ((R+r:Nat),(C+c:Nat)) 1)==3) (M r c) (bitAt F w (shift ((R+r:Nat),(C+c:Nat)) 1)) at z
    rw [eq] at z; unfold Down; rw [norm _ _ (by omega) hc,norm _ _ hr hc]; exact z
  refine ⟨fun r hr c hc => H r c hr hc,fun r hr c hc => V r c hr hc,?_⟩; intro r hr c hc
  have yes : ∀ a b m n : Bool, Own a b m n → a || b → m || n := by decide
  let p := ink M r c; let d := A (r+1) (c+1)
  change active (bits p) d.val=true
  have bits' : ∀ p : Ink, ∀ k : Fin 9, (bits p).testBit k.val=p k := by native_decide
  generalize e : d=i; change A (r+1) (c+1)=i at e; fin_cases i
  · have z := yes _ _ _ _ (H (r+1) (c+1) (by omega) (by omega)) (by simp [e]); change (bits p).testBit ((4:Fin 9).val) || (bits p).testBit ((5:Fin 9).val) at ⊢; rw [bits',bits']; exact z
  · have z := yes _ _ _ _ (V (r+1) (c+1) (by omega) (by omega)) (by simp [e]); change (bits p).testBit ((4:Fin 9).val) || (bits p).testBit ((7:Fin 9).val) at ⊢; rw [bits',bits']; exact z
  · have z := yes _ _ _ _ (H (r+1) c (by omega) (by omega)) (by simp [e]); change (bits p).testBit ((4:Fin 9).val) || (bits p).testBit ((3:Fin 9).val) at ⊢; rw [bits',bits',Bool.or_comm]; exact z
  · have z := yes _ _ _ _ (V r (c+1) (by omega) (by omega)) (by simp [e]); change (bits p).testBit ((4:Fin 9).val) || (bits p).testBit ((1:Fin 9).val) at ⊢; rw [bits',bits',Bool.or_comm]; exact z

def quadAt {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (R C : Nat) : Pattern :=
  (square F w R C,square F w (R+3) C,square F w R (C+3),square F w (R+3) (C+3))

theorem avoids {u} (F : Finset (GridVertex (N u) (N u))) (Q : Flow F) (w : View) (price : Prices F w)
    (R C : Nat) (rr : 11≤R ∧ R+15≤33+42*u ∧ R%3=1) (cc : 11≤C ∧ C+15≤33+42*u ∧ C%3=1) : quadAt F w R C∉banned := by
  intro bad; let M := marksAt F w (R-3) (C-3); let A := dirsAt Q w (R-3) (C-3)
  obtain ⟨east,south,active⟩ := rect F Q w price (R-3) (C-3) 12 12 (by omega) (by omega)
  apply impossible _ bad M A (fun r hr c hc => east r hr c (by omega)) (fun r hr c hc => south r (by omega) c hc) _ (fun r hr c hc => active r (by omega) c (by omega))
  swap
  · intro r hr c hc; dsimp only [M]; rw [sq]
    simpa only [show (R-3+r)%3=(r+1)%3 by omega,show (C-3+c)%3=(c+1)%3 by omega] using price (R-3+r) (C-3+c) (by omega) (by omega) (by omega) (by omega)
  intro y hy x hx; let k : Fin 9 := ⟨3*(y%3)+x%3,by omega⟩
  have get (b a : Nat) : (square F w b a).testBit k.val=bitAt F w ((b+k.val/3:Nat),(a+k.val%3:Nat)) := maskbits _ k
  change _=(maskOf _ y x).testBit k.val; unfold maskOf quadAt; dsimp only; split_ifs <;> rw [get] <;> unfold M marksAt <;> congr 1 <;> apply Prod.ext <;> dsimp [k] <;> omega
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
