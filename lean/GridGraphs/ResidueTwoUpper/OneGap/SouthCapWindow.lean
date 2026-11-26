import GridGraphs.ResidueTwoUpper.OneGap.SouthCapWitness

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open L7 ResidueZero Stencil

/-- Only atlas offsets that are on the board carry variables. -/
abbrev Slots (h w r c : Nat) :=
  {x : Fin 18 × Fin 18 // atlasSite h r x.1 < 119 ∧ atlasSite w c x.2 < 119}

structure Placement (u k h w r c : Nat) : Prop where
  size : k=11+14*u
  wide : 53 ≤ k
  height : h+4 ≤ k
  width : w+4 ≤ k
  row : r+2 ≤ h
  col : c+2 ≤ w

namespace Placement
variable {u k h w r c : Nat} (pl : Placement u k h w r c)

def point (v : View) (x : Slots h w r c) : Site u :=
  onSite (L7.view v (35+42*u:Nat) (haloSite k h r x.1.1) (haloSite k w c x.1.2))
    (inside_view v
      ((halo_site_geometry pl.size pl.wide pl.height pl.row (by have := x.1.1.isLt; omega)).2.2.1.mpr x.2.1)
      ((halo_site_geometry pl.size pl.wide pl.width pl.col (by have := x.1.2.isLt; omega)).2.2.1.mpr x.2.2))

@[simp] theorem point_coord (v : View) (x : Slots h w r c) :
    coord (pl.point v x)=L7.view v (35+42*u:Nat)
      (haloSite k h r x.1.1) (haloSite k w c x.1.2) := coord_onSite ..

theorem point_injective (v : View) : Function.Injective (pl.point v) := by
  intro x y eq
  have coords := congrArg coord eq
  simp only [point_coord] at coords
  apply Subtype.ext; apply Prod.ext <;> apply Fin.ext
  all_goals
    cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [L7.view,reflect,Prod.mk.injEq,haloSite] at coords <;> omega

/-- Physical adjacency is exactly the adjacency of the window offsets,
including when both coordinates read a reflected or swapped axis. -/
theorem point_adj (v : View) (x y : Slots h w r c) :
    (gridGraph (35+42*u) (35+42*u)).Adj (pl.point v x) (pl.point v y) ↔
      adjacent 18 18 x.1 y.1 := by
  have X := pl.point_coord v x
  have Y := pl.point_coord v y
  change adjacent _ _ _ _ ↔ _
  simp only [adjacent, Fin.ext_iff]
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [coord,L7.view,reflect,Prod.mk.injEq,haloSite] at X Y <;> omega

/-- The catalogue's prescribed root is represented by exactly the
offset whose two atlas coordinates lie on the far rim. -/
theorem point_root (v : View) (x : Slots h w r c) :
    pl.point v x=seSite u v ↔ atlasSite h r x.1.1=118 ∧ atlasSite w c x.1.2=118 := by
  have X := (halo_site_geometry pl.size pl.wide pl.height pl.row
    (d:=x.1.1.val) (by have := x.1.1.isLt; omega)).2.2.2.2 0 (by decide)
  have Y := (halo_site_geometry pl.size pl.wide pl.width pl.col
    (d:=x.1.2.val) (by have := x.1.2.isLt; omega)).2.2.2.2 0 (by decide)
  rw [←coord_injective.eq_iff,point_coord,seSite,coord_onSite]
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [L7.view,reflect,Prod.mk.injEq] <;> omega

end Placement

structure WindowField (V : Type) where
  mark : V → Bool
  arrow : V → V → Bool
  sheet : V → Bool

local instance (a b : GridVertex 18 18) : Decidable (adjacent 18 18 a b) := by
  unfold adjacent
  infer_instance

/-- Restrict the *same* parent and sheet maps, rather than reconstructing
the forest separately in each of the overlapping windows. -/
def windowField {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) : WindowField (Slots h w r c) where
  mark x := decide (pl.point v x ∈ F)
  arrow x y := decide (x ≠ y ∧ H.parent (pl.point v x)=pl.point v y)
  sheet x := H.sheet (pl.point v x)

theorem window_root {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y : Slots h w r c)
    (root : atlasSite h r x.1.1=118 ∧ atlasSite w c x.1.2=118) :
    (windowField pl H).arrow x y=false := by
  have fx : H.parent (pl.point v x)=pl.point v x := by
    rw [(pl.point_root v x).mpr root,H.root]
  simp only [windowField,fx,decide_eq_false_iff_not]
  exact fun ⟨ne,eq⟩ => ne (pl.point_injective v eq)

/-- The Boolean edge clauses in the window: a forced edge has exactly
one owner, and a free or missing edge has none. -/
theorem window_edges {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y : Slots h w r c) :
    ((windowField pl H).arrow x y || (windowField pl H).arrow y x) =
      decide (adjacent 18 18 x.1 y.1 ∧
        ((windowField pl H).mark x || (windowField pl H).mark y)=true) ∧
    ((windowField pl H).arrow x y && (windowField pl H).arrow y x)=false := by
  let W := windowField pl H
  have ok (a b : Slots h w r c) (e : W.arrow a b=true) :
      (Bonds F).Adj (pl.point v a) (pl.point v b) := by
    have e' : a≠b ∧ H.parent (pl.point v a)=pl.point v b := of_decide_eq_true e
    rw [←e'.2]
    exact H.step _ (fun z => e'.1 (pl.point_injective v (e'.2.symm.trans z).symm))
  have fork : (Bonds F).Adj (pl.point v x) (pl.point v y) ↔
      adjacent 18 18 x.1 y.1 ∧ (W.mark x=true ∨ W.mark y=true) := by
    change (_ ∧ (_ ∨ _)) ↔ _
    rw [pl.point_adj]
    simp [W,windowField]
  have disj (a b : Slots h w r c) (e : W.arrow a b=true) : W.arrow b a=false := by
    have a' : a≠b ∧ H.parent (pl.point v a)=pl.point v b := of_decide_eq_true e
    have h := (H.covers _ _ (ok _ _ e)).mp a'.2
    exact decide_eq_false (fun z => h z.2)
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (e|e)
      · exact fork.mp (ok _ _ e)
      · exact fork.mp (ok _ _ e).symm
    · intro e
      have edge := fork.mpr e
      have ne : x≠y := fun h => edge.ne (congrArg (pl.point v) h)
      by_cases a : H.parent (pl.point v x)=pl.point v y
      · exact Or.inl (decide_eq_true ⟨ne,a⟩)
      · have b : H.parent (pl.point v y)=pl.point v x := by
          by_contra h; exact a ((H.covers _ _ edge).mpr h)
        exact Or.inr (decide_eq_true ⟨Ne.symm ne,b⟩)
  · cases e : W.arrow x y
    · rfl
    · change (true && W.arrow y x)=false
      exact disj x y e

theorem window_turn {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (x y z : Slots h w r c)
    (xy : (windowField pl H).arrow x y=true) (yz : (windowField pl H).arrow y z=true) :
    (windowField pl H).sheet y=xor ((windowField pl H).sheet x) (decide
      ((dir (pl.point v x) (pl.point v y)=0 ∧ dir (pl.point v y) (pl.point v z)=3) ∨
       (dir (pl.point v x) (pl.point v y)=3 ∧ dir (pl.point v y) (pl.point v z)=0))) := by
  have a : x≠y ∧ H.parent (pl.point v x)=pl.point v y := of_decide_eq_true xy
  have b : y≠z ∧ H.parent (pl.point v y)=pl.point v z := of_decide_eq_true yz
  exact H.turns _ _ _ a.2 (fun e => a.1 (pl.point_injective v e))
    b.2 (fun e => b.1 (pl.point_injective v e))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
