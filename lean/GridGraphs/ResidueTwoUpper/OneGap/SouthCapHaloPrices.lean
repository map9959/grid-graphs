import GridGraphs.ResidueTwoUpper.OneGap.SouthCapHalo
import GridGraphs.ResidueTwoUpper.ExceptionalBudget

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7

/-- In the southeast halo the aligned row is strictly below the
isolated star's row. This includes the six-site margin above the crop. -/
theorem halo_below_defect {k extent i d : Nat} (_hk : 53 ≤ k)
    (he : extent+4 ≤ k) : 2 < haloSite k extent i d := by
  unfold haloSite
  omega

/-- Each complete physical patch and its central star supply exactly
the zero-price tests at the corresponding atlas coordinates. The
orientation is the one used to state the physical slack, not a
separately selected outgoing direction for each atlas window. -/
theorem halo_zero_prices {u k h w r c d e : Nat} (ke : k=11+14*u) (hk : 53 ≤ k)
    (hh : h+4 ≤ k) (hw : w+4 ≤ k) (hr : r+2 ≤ h) (hc : c+2 ≤ w)
    (hd : d ≤ 15) (he : e ≤ 15)
    (R : haloSite k h r d < 33+42*u) (C : haloSite k w c e < 33+42*u)
    (v : View) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (a : origins (35+42*u)) (p : GridVertex (35+42*u) (35+42*u))
    (ha : coord a=L7.view v (33+42*(u:Int)) (haloSite k h r d) (haloSite k w c e))
    (hp : coord p=coord a+(1,1))
    (clean : patchSlack F a=0) (q : Nat)
    (only : ∀ x, coord x≠L7.view v (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P x=0) :
    twoOrbitPatch 119 (L7.view v 117 (atlasSite h r d) (atlasSite w c e)) (maskAt F a)=0 ∧
    twoOrbitStar 119 (L7.view v 119 ((atlasSite h r d:Int)+1) ((atlasSite w c e:Int)+1))
      (if p∈F then 1 else 0) (neighbours F (coord p)) (outDir p (P p))=0 := by
  classical
  have ar : Align u (haloSite k h r d) (atlasSite h r d) :=
    (halo_origins ke hk hh hr hd).2 R
  have ac : Align u (haloSite k w c e) (atlasSite w c e) :=
    (halo_origins ke hk hw hc he).2 C
  have N : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; ring
  have ep : coord p = L7.view v (35+42*(u:Int))
      ((haloSite k h r d:Int)+1) ((haloSite k w c e:Int)+1) := by
    rw [hp,ha,show (33+42*(u:Int))=35+42*(u:Int)-2 by ring,view_center]
  have neq : coord p≠L7.view v (35+42*(u:Int)) 2 (2+3*q:Nat) := by
    rw [ep]; intro bad
    have below := halo_below_defect (i:=r) (d:=d) hk hh
    cases v with | mk a b s =>
      cases a <;> cases b <;> cases s <;> simp [L7.view,reflect,Prod.mk.injEq] at bad <;> omega
  have price := atlas_prices ar ac v (maskAt F a) (if p∈F then 1 else 0)
    (neighbours F (coord p)) (outDir p (P p))
  constructor
  · rw [←price.1,←ha,←N]
    exact clean
  · rw [←price.2,←ep,←N]
    by_cases mem : p∈F <;> simpa [starSlack,mem] using only p neq

/-- Direct representative agreement for stars, including those on the
rim which are not the centres of any complete patch. -/
private theorem rim_star_axis {u k extent i d : Nat} (ke : k=11+14*u) (hk : 53 ≤ k)
    (he : extent+4 ≤ k) (hi : i+2 ≤ extent) (hd : d ≤ 17)
    (far : Bool) :
    rep 23 (4+14*(u:Int)) (reflect far (35+42*(u:Int)) (haloSite k extent i d)) =
      rep 23 32 (reflect far 119 (atlasSite extent i d)) := by
  cases far <;> simp only [reflect, Bool.false_eq_true, if_false, if_true] <;>
    unfold rep haloSite atlasSite endTag repTile <;> split_ifs <;> omega

theorem halo_star_price_transport {u k h w r c d e : Nat}
    (ke : k=11+14*u) (hk : 53 ≤ k) (hh : h+4 ≤ k) (hw : w+4 ≤ k)
    (hr : r+2 ≤ h) (hc : c+2 ≤ w) (hd : d ≤ 17) (he : e ≤ 17)
    (v : View) (f nb o : Nat) :
    twoOrbitStar (35+42*(u:Int))
      (L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e)) f nb o =
    twoOrbitStar 119 (L7.view v 119 (atlasSite h r d) (atlasSite w c e)) f nb o := by
  have same : representative 23 (4+14*(u:Int))
      (L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e)) =
      representative 23 32 (L7.view v 119 (atlasSite h r d) (atlasSite w c e)) := by
    have R := rim_star_axis ke hk hh hr hd
    have C := rim_star_axis ke hk hw hc he
    cases v with | mk a b s =>
      cases s <;> apply Prod.ext <;> first | exact R _ | exact C _
  have loc (g : Nat) :
      starLocation (35+42*(u:Int))
        (image (35+42*(u:Int)) g (L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e))) =
      starLocation 119 (image 119 g (L7.view v 119 (atlasSite h r d) (atlasSite w c e))) := by
    have X := starLocation_transport (b:=23) (j:=4+14*(u:Int)) (by decide) (by positivity)
      (L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e)) g
    have Y := starLocation_transport (b:=23) (j:=32) (by decide) (by decide)
      (L7.view v 119 (atlasSite h r d) (atlasSite w c e)) g
    rw [show (23:Int)+3*(4+14*(u:Int))=35+42*(u:Int) by ring] at X
    rw [show (23:Int)+3*32=119 by decide] at Y
    exact X.trans ((congrArg (fun p => starLocation 23 (image 23 g p)) same).trans Y.symm)
  simp only [twoOrbitStar, loc]

/-- Clean roots and arrows are transported unchanged: this statement
does not choose a new root in the atlas or assume root invariance. -/
theorem halo_rim_star_zero {u k h w r c d e : Nat}
    (ke : k=11+14*u) (hk : 53 ≤ k) (hh : h+4 ≤ k) (hw : w+4 ≤ k)
    (hr : r+2 ≤ h) (hc : c+2 ≤ w) (hd : d ≤ 17) (he : e ≤ 17)
    (v : View) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (p : GridVertex (35+42*u) (35+42*u))
    (hp : coord p=L7.view v (35+42*(u:Int)) (haloSite k h r d) (haloSite k w c e))
    (q : Nat)
    (only : ∀ x, coord x≠L7.view v (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P x=0) :
    twoOrbitStar 119 (L7.view v 119 (atlasSite h r d) (atlasSite w c e))
      (decide (p∈F)).toNat (neighbours F (coord p)) (outDir p (P p))=0 := by
  have neq : coord p≠L7.view v (35+42*(u:Int)) 2 (2+3*q:Nat) := by
    rw [hp]; intro bad
    have below := halo_below_defect (i:=r) (d:=d) hk hh
    cases v with | mk a b s =>
      cases a <;> cases b <;> cases s <;> simp [L7.view,reflect,Prod.mk.injEq] at bad <;> omega
  rw [←halo_star_price_transport ke hk hh hw hr hc hd he v, ←hp,
    ←show ((35+42*u:Nat):Int)=35+42*(u:Int) by push_cast; ring]
  exact only p neq

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
