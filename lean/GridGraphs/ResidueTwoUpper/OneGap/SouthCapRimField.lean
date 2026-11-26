import GridGraphs.ResidueTwoUpper.OneGap.SouthCapRoot
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapRim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open L7 ResidueZero Stencil TwoGap.Words BoundarySix.Connected GridGraphs.ResidueTwoUpper.Exceptional.Frame

/-- Read up from the south rim, keeping the west-to-east order. -/
def southView (v : View) : View :=
  if v.swap then {v with colFar := !v.colFar} else {v with rowFar := !v.rowFar}

theorem south_coords (v : View) (n r c : Int) :
    view (southView v) n r c = view v n (n-1-r) c := by
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;> ext <;> simp [southView,L7.view,reflect]

@[simp] theorem south_otherEnd (v : View) :
    otherEnd (southView v) = (!v.rowFar,!v.colFar) := by
  cases v with | mk a b s => cases s <;> rfl

/-- Both preset strips are read from the original marks. The near
corner of either reflected strip is outside the retained portion;
the far corner is the same closed southeast corner in both strips. -/
theorem actual_rim_strips {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (v : View) (s f : Bool) (seed : rim F v s f) :
    ∃ a : Bool,
      (∀ r j : Nat, 3≤j → r<7 → j<35+42*u → ∀ m,
        preset (35+42*u) false a r j=some m →
        marked F (view (southView v) (35+42*u:Nat) r j)=m) ∧
      (∀ r j : Nat, 3≤j → r<7 → j<35+42*u → ∀ m,
        preset (35+42*u) false (!a) r j=some m →
        marked F (view (southView (turnView v)) (35+42*u:Nat) r j)=m) := by
  let n := 35+42*u
  have hn : 35≤n := by dsimp [n]; omega
  have closed := (southeast_closed F acy score one v s f seed).1
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  have geo (x) := star_geometry hn F P step x (good (.inl x))
  have words := physicalWord_ok hn F P good (!v.rowFar,!v.colFar)
  have strip (w : View) (eq : otherEnd w = (!v.rowFar,!v.colFar)) :
      ∃ a : Bool, ∀ r j : Nat, 3≤j → r<7 → j<n → ∀ m,
        preset n false a r j=some m → marked F (view w (n:Nat) r j)=m := by
    apply realize_on hn F w false (fun j => 3≤j) (corners_marked u F acy score)
      (fun x => (geo x).1) (fun x => (geo x).2.1)
    · intro i _ hi; have := i.isLt; omega
    · omega
    · rw [eq]; exact closed
    · rw [eq]; exact words
  obtain ⟨a,ha⟩ := strip (southView v) (south_otherEnd v)
  obtain ⟨b,hb⟩ := strip (southView (turnView v)) (by simp [turnView])
  have first := ha 1 (n-1) (by omega) (by decide) (by omega) (!a)
    (by simp [preset,show n-1≠0 by omega,show n-1+1=n by omega])
  have second := hb 0 (n-2) (by omega) (by decide) (by omega) b
    (by simp [preset,show n-2≠1 by omega,show n-2≠2 by omega,show n-2+2=n by omega])
  have shared : L7.view (southView v) (n:Nat) 1 ((n-1:Nat):Int) =
      L7.view (southView (turnView v)) (n:Nat) 0 ((n-2:Nat):Int) := by
    rw [south_coords,south_coords,turned]
    congr 1 <;> omega
  norm_num at first second
  rw [shared,second] at first
  exact ⟨a,ha,first ▸ hb⟩

/-- The frame literals in the finite atlas window are satisfied by
the actual halo, with one consistent choice of the corner pattern. -/
theorem atlas_rim_strips {u k h w r c} (ke : k=11+14*u) (hk : 53≤k)
    (hh : h+4≤k) (hw : w+4≤k) (hr : r+2≤h) (hc : c+2≤w)
    (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (v : View) (s f : Bool) (seed : rim F v s f) :
    ∃ a : Bool, ∀ d e : Nat, d≤17 → e≤17 →
      let X := atlasSite h r d
      let Y := atlasSite w c e
      let bit := marked F (L7.view v (35+42*u:Nat) (haloSite k h r d) (haloSite k w c e))
      X<119 → Y<119 → ∀ t : Nat, t≤6 →
        (X+t+1=119 → ∀ m, preset 119 false a t Y=some m → bit=m) ∧
        (Y+t+1=119 → ∀ m, preset 119 false (!a) t X=some m → bit=m) := by
  obtain ⟨a, south, east⟩ := actual_rim_strips F acy score one v s f seed
  refine ⟨a, ?_⟩
  intro d e hd he X Y bit xIn yIn t ht
  let n := 35+42*u
  let x := haloSite k h r d
  let y := haloSite k w c e
  have gx := halo_site_geometry ke hk hh hr hd
  have gy := halo_site_geometry ke hk hw hc he
  have xb : 3≤x := halo_below_defect hk hh
  have yb : 3≤y := halo_below_defect hk hw
  have lo {extent i j} (fit : i+2≤extent) : 3≤atlasSite extent i j := by
    unfold atlasSite repTile endTag; split_ifs <;> omega
  have move (z Z : Nat) (p : Bool) (loz : 3≤z) (loZ : 3≤Z)
      (h1 : z+1=n ↔ Z+1=119) (h2 : z+2=n ↔ Z+2=119) :
      preset n false p t z=preset 119 false p t Z := by
    have z0 : z≠0 := by omega
    have Z0 : Z≠0 := by omega
    simp only [preset,z0,Z0,if_false,h1,h2,show z≠1 by omega,show Z≠1 by omega,
      show z≠2 by omega,show Z≠2 by omega,false_or]
  constructor
  · intro hit m hm
    have edge := (gx.2.2.2.2 t ht).mpr hit
    have fix := south t y yb (by omega) (gy.2.2.1.mpr yIn) m
      ((move y Y a yb (lo hc) (gy.2.2.2.2 0 (by decide)) (gy.2.2.2.2 1 (by decide))).trans hm)
    rw [south_coords] at fix
    have coord : (n:Int)-1-t=(x:Int) := by omega
    change marked F (L7.view v (n:Int) ((n:Int)-1-t) y)=m at fix
    rw [coord] at fix
    exact fix
  · intro hit m hm
    have edge := (gy.2.2.2.2 t ht).mpr hit
    have fix := east t x xb (by omega) (gx.2.2.1.mpr xIn) m
      ((move x X (!a) xb (lo hr) (gx.2.2.2.2 0 (by decide)) (gx.2.2.2.2 1 (by decide))).trans hm)
    rw [south_coords,turned] at fix
    have coord : (n:Int)-1-t=(y:Int) := by omega
    change marked F (L7.view v (n:Int) x ((n:Int)-1-t))=m at fix
    rw [coord] at fix
    exact fix

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
