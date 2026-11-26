import GridGraphs.ResidueTwoUpper.OneGap.FanFlow

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
open ResidueZero Stencil L7 FanSlab FanSeed BoundarySix.Connected
local macro "metric" : tactic => `(tactic| first | omega | (simp only [abs_eq_max_neg] at * <;> omega))

def In (n : Nat) (p : Pos) := 0≤p.1 ∧ p.1<n ∧ 0≤p.2 ∧ p.2<n
instance (n p) : Decidable (In n p) := by unfold In; infer_instance
def point (u : Nat) (w : View) (p : Pos) : GridVertex (35+42*u) (35+42*u) := if h : In (35+42*u) p then
  atDepth w p.1.toNat p.2.toNat (by unfold In at h; omega) (by unfold In at h; omega) else nw u

theorem coords_view {n} (w : View) (v : GridVertex n n) : L7.view w n (coordinates w v).1 (coordinates w v).2=coord v := by
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> ext <;> simp [coordinates,L7.view,reflect]
theorem view_inj (w : View) (n : Int) {x y : Pos} (e : L7.view w n x.1 x.2=L7.view w n y.1 y.2) : x=y := by
  obtain ⟨a,b⟩ := x; obtain ⟨c,d⟩ := y; cases w with | mk z t s => cases z <;> cases t <;> cases s <;> simp [L7.view,reflect,Prod.mk.injEq] at * <;> omega
theorem coords_point {u w p} (hin : In (35+42*u) p) : coordinates w (point u w p)=p := by
  apply view_inj w (35+42*u:Nat); rw [coords_view]; unfold point; rw [dif_pos hin]
  rw [show coord (atDepth w p.1.toNat p.2.toNat _ _)=_ from coord_onSite ..]; unfold In at hin; congr 1 <;> omega
theorem coord_point {u w p} (hin : In (35+42*u) p) : coord (point u w p)=L7.view w (35+42*u:Nat) p.1 p.2 := by rw [←coords_view w,coords_point hin]
theorem point_inj (w : View) {n} {x y : GridVertex n n} (e : coordinates w x=coordinates w y) : x=y := by
  apply coord_injective; rw [←coords_view w x,←coords_view w y,e]

theorem adj_iff {n} (w : View) (x y : GridVertex n n) : (gridGraph n n).Adj x y ↔
    |(coordinates w x).1-(coordinates w y).1|+|(coordinates w x).2-(coordinates w y).2|=1 := by
  change adjacent .. ↔ _; unfold adjacent; simp only [Fin.ext_iff]
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [coordinates,coord,reflect] <;> metric

def bitAt {u} (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) (p : Pos) := marked F (L7.view w (35+42*u:Nat) p.1 p.2)
def way (p s : Pos) := if p=s then 4 else if p.2<s.2 then 0 else if p.1<s.1 then 1 else if s.2<p.2 then 2 else 3
def arrow {u} (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u)) (w : View) (p : Pos) := way p (coordinates w (P (point u w p)))
private theorem axis (p s : Pos) (d : Fin 4) (near : p=s ∨ |p.1-s.1|+|p.2-s.2|=1) : way p s=d.val ↔ s=shift p d := by
  rcases p with ⟨a,b⟩; rcases s with ⟨x,y⟩
  have choices : (x=a ∧ y=b) ∨ (x=a ∧ y=b+1) ∨ (x=a+1 ∧ y=b) ∨ (x=a ∧ y=b-1) ∨ (x=a-1 ∧ y=b) := by
    simp only [Prod.mk.injEq,abs_eq_max_neg] at near; omega
  rcases choices with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> fin_cases d <;> simp [way,shift,Prod.mk.injEq] <;> grind

theorem going {u w p} {P : GridVertex (35+42*u) (35+42*u) → _} {F : Finset (GridVertex (35+42*u) (35+42*u))}
    (step : ∀ v,P v≠v → (Bonds F).Adj v (P v)) (d : Fin 4) (hin : In (35+42*u) p) (hout : In (35+42*u) (shift p d)) :
    arrow P w p=d.val ↔ P (point u w p)=point u w (shift p d) := by
  let v := point u w p
  have e := coords_point (w:=w) hin; change coordinates w v=p at e
  have near : p=coordinates w (P v) ∨ |p.1-(coordinates w (P v)).1|+|p.2-(coordinates w (P v)).2|=1 := by
    by_cases f : P v=v
    · left; rw [f,e]
    · right; simpa only [e] using (adj_iff w v (P v)).mp (step _ f).1
  unfold arrow; rw [axis _ _ _ near]; constructor
  · intro e; apply point_inj w; rwa [coords_point hout]
  · intro e; rw [e,coords_point hout]

theorem cross {u w p} {P : GridVertex (35+42*u) (35+42*u) → _} {F : Finset (GridVertex (35+42*u) (35+42*u))}
    (step : ∀ v,P v≠v → (Bonds F).Adj v (P v)) (owners : ∀ v z,(Bonds F).Adj v z → (P v=z ↔ P z≠v))
    (d : Fin 4) (hin : In (35+42*u) p) (hout : In (35+42*u) (shift p d)) :
    let x := arrow P w p==d.val; let y := arrow P w (shift p d)==(d.val+2)%4
    (x != y) == (bitAt F w p || bitAt F w (shift p d)) && !(x && y) := by
  dsimp only; let v := point u w p; let z := point u w (shift p d)
  have rev : shift (shift p d) ((d.val+2)%4)=p := by fin_cases d <;> ext <;> simp [shift]
  have x := going (w:=w) step d hin hout
  have y := going (w:=w) step ⟨(d.val+2)%4,by omega⟩ hout (rev ▸ hin); rw [rev] at y
  have adj : (gridGraph _ _).Adj v z := by rw [adj_iff w,coords_point hin,coords_point hout]; fin_cases d <;> simp [shift]
  have forced : (Bonds F).Adj v z ↔ bitAt F w p || bitAt F w (shift p d) := by
    change (_ ∧ (_ ∨ _)) ↔ _; simp only [adj,true_and,bitAt,←coord_point (w:=w) hin,←coord_point (w:=w) hout,marked_at,Bool.or_eq_true,decide_eq_true_eq]; rfl
  have ne := adj.ne
  change (arrow P w p=d.val ↔ P v=z) at x; change (arrow P w (shift p d)=(d.val+2)%4 ↔ P z=v) at y
  by_cases h : (Bonds F).Adj v z
  · have iff := owners _ _ h; rw [forced.mp h]; by_cases A : P v=z <;> simp_all
  · have e : (bitAt F w p || bitAt F w (shift p d))=false := Bool.eq_false_iff.mpr (fun g => h (forced.mpr g))
    have a : P v≠z := fun eq => h (eq ▸ step v (by rw [eq]; exact ne.symm))
    have b : P z≠v := fun eq => h (eq ▸ (step z (by rw [eq]; exact ne)).symm)
    simp [e,show arrow P w p≠d.val from fun e => a (x.mp e),show arrow P w (shift p d)≠(d.val+2)%4 from fun e => b (y.mp e)]
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Camera
