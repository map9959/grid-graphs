import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapArithmetic
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapBank

/-! What the long-fan handoff actually supplies to a southern cap.
Indices in this file count aligned tiles, not physical sites. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open L7 FanSlab FanSeed Camera Port ResidueZero Stencil BoundarySix.Connected

theorem star_clean_on_crop {u q h : Nat} {F : Finset (GridVertex (N u) (N u))}
    (w : View) (P : GridVertex (N u) (N u) → _) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43)
    (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (p : GridVertex (N u) (N u)) {r c : Nat}
    (depth : firstRow (11+14*u) h-1≤r) (pos : coord p=L7.view w (N u) r c) :
    starSlack F P p=0 := by
  apply zero p
  intro bad
  rw [pos] at bad
  have ns : ((N u:Nat):Int)=35+42*(u:Int) := by unfold N; push_cast; ring
  rw [ns] at bad
  have eq : ((r:Int),(c:Int)) = (2,((2+3*q:Nat):Int)) :=
    view_inj w (35+42*(u:Int)) bad
  have contra := congrArg Prod.fst eq
  have z := (crop_bounds (11+14*u) rfl hk lo hi).1
  dsimp only at contra
  omega

/-- Localized, strictly weaker input than `Front`: only the last tooth's
history is needed. `q+2≤k` and the long-index bound are from the handoff,
not fields of `SouthEnd`. -/
theorem physical_input {u q} {F : Finset (GridVertex (N u) (N u))} {w : View}
    (big : 57≤q) (fit : q+2≤11+14*u) (south : SouthEnd F w q) :
    let k := 11+14*u
    ∃ h, 14≤h ∧ h≤43 ∧ h≤k ∧ width h≤k ∧
      (∀ i, k - width h ≤ i → i < k → square F w (1+3*(k-h)) (1+3*i)=73) ∧
      RootLine F w (k-1) (k-h) := by
  dsimp only
  obtain ⟨h,f,⟨lo,hi,room⟩,row,_,roots⟩ := south
  change f+3*h/4+3≤11+14*u at room
  refine ⟨h,lo,hi,by omega,by unfold width; omega,?_,?_⟩
  · intro i st en; apply row _ le_rfl le_rfl i _ en; unfold width at st; omega
  · apply roots <;> omega

/-- The last top contact even gives an arrow in the *physical* flow;
the other contacts need no prescribed outgoing directions. -/
theorem scored_input {u q} (F : Finset (GridVertex (N u) (N u))) (w : View)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (big : 57≤q) (fit : q+2≤11+14*u)
    (south : SouthEnd F w q) :
    let k := 11+14*u
    ∃ (Q : Flow F) (h : Nat), 14≤h ∧ h≤43 ∧
      (∀ i, k - width h ≤ i → i < k → square F w (1+3*(k-h)) (1+3*i)=73) ∧
      arrow Q.parent w (1+3*((k-h:Nat):Int),1+3*((k-1:Nat):Int))=3 := by
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  obtain ⟨h,lo,hi,hk,_,top,line⟩ := physical_input big fit south
  exact ⟨Q,h,lo,hi,top,root_tip F w Q _ _ (by unfold N; omega) (by unfold N; omega) line⟩

/-- The axis test from `ordered_seam_price.table`, with both axes imposed.
The Python word is transposed relative to `square`; the union of the two
opposite pairs of neighbors is invariant under transposition. -/
def bothAxes (m : Nat) : Prop := m &&& 16 = 0 ∨ m &&& 170 = 0
instance (m : Nat) : Decidable (bothAxes m) := by unfold bothAxes; infer_instance

def filteredCap {n} (F : Finset (GridVertex n n)) (w : View) (k h : Nat) :=
  ∀ j i : Nat, k - h ≤ j → j < k → k - width h ≤ i → i < k →
    4 ≤ i → i + 5 ≤ k → 4 ≤ j → j + 5 ≤ k → bothAxes (square F w (1+3*j) (1+3*i))

theorem shape_axes {m : Nat} (h : m∈shapes) : bothAxes m := by
  have all : ∀ a∈shapes, bothAxes a := by decide
  exact all _ h

/-- Even if the deep hypothesis is separately supplied at the cap, its
upper limits are `+7`, whereas the axis filter reaches `+5`. -/
theorem axes_of_deep {u} {F : Finset (GridVertex (N u) (N u))} {w : View} {y j i : Nat}
    (deep : DeepAfter F w y) (yj : y ≤ j) (js : j + 7 ≤ 11+14*u) (iw : 4 ≤ i) (ie : i + 7 ≤ 11+14*u) :
    bothAxes (square F w (1+3*j) (1+3*i)) := shape_axes (deep j i yj js iw ie)

/-- The missing physical admission theorem for the axis-free external
replay. Use `widened bank` for the ordinary 49-tag plaquette catalogue
augmented for the second closed southeast word. Coordinate order is NW, NE, SW, SE, and masks
are row-major. This assertion concerns just the cropped rectangle. It
does not assert any plateau or propagation result north of the crop.

The external bank was generated with a prescribed frame and perimeter
orientation; membership is not an immediate consequence of an abstract
`Front`. `star_clean_on_crop` only handles the location of the priced
exception, not the frame or the catalogue implication. -/
def CropAdmitted {n} (bank : Nat → Nat → Word → Prop)
    (F : Finset (GridVertex n n)) (w : View) (k h : Nat) : Prop :=
  ∀ r c : Nat, r+2≤h → c+2≤width h →
    let R := firstRow k h+3*r
    let C := firstCol k h+3*c
    bank (endTag h r) (endTag (width h) c)
      (square F w R C,square F w R (C+3),square F w (R+3) C,square F w (R+3) (C+3))

abbrev OrdinaryCapAdmitted {n} (F : Finset (GridVertex n n)) (w : View) (k h : Nat) :=
  CropAdmitted (widened ordinary) F w k h

/-- In the smallest requested rectangle, at (x,y)=(8,9), both chart
tags are 34. The ordered catalogue admits (24,3,12,3) on axis 1 but
not on axis 2. Here it is in physical row-major order (NW,SW,NE,SE).
Even all 16 overlapping zero-price mask tests of `Port.markOK` admit
it. This is a *local* witness, not a scored forest counterexample. -/
theorem missing_filter_witness : Port.markOK 18 9 66 9 ∧
    (18 &&& 40 : Nat)=0 ∧ ¬bothAxes 18 := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
