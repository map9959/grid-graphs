import GridGraphs.ResidueTwoUpper.OneGap.SouthCapRimField
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapTurns

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open L7 ResidueZero Stencil GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected

abbrev Site (u : Nat) := GridVertex (35+42*u) (35+42*u)

def seSite (u : Nat) (v : View) : Site u :=
  onSite (L7.view v (35+42*u:Nat) (34+42*u:Nat) (34+42*u:Nat))
    (inside_view v (by omega) (by omega))

private theorem se_corner (u : Nat) (v : View) : isCorner (seSite u v) := by
  have eq : coord (seSite u v) = L7.view v (35+42*u:Nat) (34+42*u:Nat) (34+42*u:Nat) :=
    coord_onSite ..
  unfold isCorner
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [coord,L7.view,reflect,Prod.mk.injEq] at eq <;> omega

structure PhysicalHalo (u : Nat) (F : Finset (Site u)) (v : View) (q : Nat)
    (dir : Site u → Site u → Nat) where
  parent : Site u → Site u
  sheet : Site u → Bool
  cornerBit : Bool
  root : parent (seSite u v)=seSite u v
  step : ∀ x, parent x≠x → (Bonds F).Adj x (parent x)
  covers : ∀ x y, (Bonds F).Adj x y → (parent x=y ↔ parent y≠x)
  exits : exitSet parent=∅
  turns : ∀ x y z, parent x=y → x≠y → parent y=z → y≠z →
    sheet y=xor (sheet x) (decide
      ((dir x y=0 ∧ dir y z=3) ∨ (dir x y=3 ∧ dir y z=0)))
  stars : ∀ x, coord x≠L7.view v (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F parent x=0
  patches : ∀ a, patchSlack F a=0
  south : ∀ t j : Nat, 3≤j → t<7 → j<35+42*u → ∀ m,
    preset (35+42*u) false cornerBit t j=some m →
    marked F (L7.view (southView v) (35+42*u:Nat) t j)=m
  east : ∀ t j : Nat, 3≤j → t<7 → j<35+42*u → ∀ m,
    preset (35+42*u) false (!cornerBit) t j=some m →
    marked F (L7.view (southView (turnView v)) (35+42*u:Nat) t j)=m

/-- Package a single southeast-rooted field for all windows. In
particular rerooting keeps the *located* defect from the fan input,
which is needed to know that its halo prices really are zero. -/
theorem physical_halo (u : Nat) (F : Finset (Site u))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (v : View) (s f : Bool) (rim : L7.rim F v s f)
    (q : Nat) (old : Site u → Site u) (d : Site u)
    (iso : (Bonds F).IsIsolated d)
    (pos : coord d=L7.view v (35+42*u:Nat) 2 (2+3*q:Nat))
    (oldStep : ∀ x, old x≠x → (Bonds F).Adj x (old x))
    (oldZero : ∀ x, x≠d → starSlack F old x=0) (dir : Site u → Site u → Nat) :
    Nonempty (PhysicalHalo u F v q dir) := by
  have c := se_corner u v
  let root : PerimeterVertex (35+42*u) := ⟨seSite u v, c.1.elim Or.inl (Or.inr ∘ Or.inl)⟩
  obtain ⟨P,rank,fix,edge,cover,exits,_,stars,patches,down⟩ :=
    rim_root_at_defect u F acy score one root c old d iso oldStep oldZero
  obtain ⟨sheet,turns⟩ := compass_sheet P rank down dir
  obtain ⟨a,south,east⟩ := actual_rim_strips F acy score one v s f rim
  refine ⟨⟨P,sheet,a,fix,edge,cover,exits,turns,?_,patches,south,east⟩⟩
  intro x notDefect
  apply stars x
  intro eq
  subst x
  exact notDefect (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using pos)

/-- Read an atlas star directly from the assembled witness. This
uses its own rerooted arrows, including on the clipped rim. -/
theorem PhysicalHalo.atlas_star {u F v q dir} (H : PhysicalHalo u F v q dir)
    {k h w r c d e : Nat} (ke : k=11+14*u) (hk : 53 ≤ k) (hh : h+4 ≤ k) (hw : w+4 ≤ k)
    (hr : r+2 ≤ h) (hc : c+2 ≤ w) (hd : d ≤ 17) (he : e ≤ 17)
    (p : Site u)
    (hp : coord p=L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e)) :
    twoOrbitStar 119 (L7.view v 119 (atlasSite h r d) (atlasSite w c e))
      (decide (p∈F)).toNat (neighbours F (coord p)) (outDir p (H.parent p))=0 :=
  halo_rim_star_zero ke hk hh hw hr hc hd he v F H.parent p hp q H.stars

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
