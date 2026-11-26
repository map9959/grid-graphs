import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripNorthWire

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 FanSeed Camera BoundarySix.Connected SimpleGraph

private theorem rim_attachment {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) (south : Bool)
    (wall : let B := prefixBox s (11+14*u) used
      (if south then B.south else B.east)=((35+42*u:Nat):Int)-1)
    (x : (prefixBox s (11+14*u) used).vertices v) (mark : x.val∈F)
    (tooth : (prefixBox s (11+14*u) used).Tooth (coordinates v x.val) south) :
    ∃ A : Attachment F ⟨x.val,prefix_site_interior v s hk lo hi used size x⟩,
      let p := coordinates v x.val
      let b := coordinates v A.rim.val
      if south then b.1=((35+42*u:Nat):Int)-1 ∧ 0<b.2 ∧ b.2<((35+42*u:Nat):Int)-1 ∧
          b.1=p.1+2 ∧ b.2=p.2
      else b.2=((35+42*u:Nat):Int)-1 ∧ 0<b.1 ∧ b.1<((35+42*u:Nat):Int)-1 ∧
          b.1=p.1 ∧ b.2=p.2+2 := by
  let B := prefixBox s (11+14*u) used
  let p := coordinates v x.val
  let n := 35+42*u
  let d : Nat := if south then 1 else 0
  let y := point u v (shift p d)
  let z := point u v (shift (shift p d) d)
  obtain ⟨xy,yz,_,cy,cz⟩ := physical_rim_wire H s hk lo hi used size south wall x mark tooth
  change coordinates v y=shift p d at cy
  change coordinates v z=shift (shift p d) d at cz
  have bounded := prefix_bounds s hk lo hi size
  obtain ⟨lr,ur,lc,uc⟩ : B.Contains p := x.2
  have ar : 4≤B.north := bounded.1
  have ac : 4≤B.west := bounded.2.1
  have er : B.south≤(n:Int)-1 := bounded.2.2.1
  have ec : B.east≤(n:Int)-1 := bounded.2.2.2
  have dep : (if south then p.1 else p.2)=(n:Int)-3 := by
    change (if south then B.south else B.east)=(n:Int)-1 at wall
    change B.Tooth p south at tooth
    cases south <;> simp [SiteBox.Tooth] at tooth wall ⊢ <;> omega
  have hy : ¬IsGridBoundary y := by
    rw [boundary_in_view v,cy]
    cases south <;> simp [d,shift] at dep ⊢ <;> omega
  have hz : IsGridBoundary z := by
    rw [boundary_in_view v,cz]
    cases south <;> simp [d,shift] at dep ⊢ <;> omega
  refine ⟨⟨⟨y,hy⟩,⟨z,hz⟩,Adj.reachable (G:=interiorGraph F) xy,yz⟩,?_⟩
  let b := coordinates v z
  change if south then b.1=(n:Int)-1 ∧ 0<b.2 ∧ b.2<(n:Int)-1 ∧
    b.1=p.1+2 ∧ b.2=p.2 else b.2=(n:Int)-1 ∧ 0<b.1 ∧ b.1<(n:Int)-1 ∧
    b.1=p.1 ∧ b.2=p.2+2
  change b=shift (shift p d) d at cz
  rw [cz]
  cases south <;> simp [d,shift] at dep ⊢ <;> omega

private def NamesRim {u : Nat} (v : View) (north x : Interior (35+42*u))
    (y : Site u) : Prop :=
  let p := coordinates v x.val
  let b := coordinates v y
  let last : Int := ((35+42*u:Nat):Int)-1
  (x=north ∧ b.1=0) ∨
    (b.1=last ∧ 0<b.2 ∧ b.2<last ∧ b.1=p.1+2 ∧ b.2=p.2) ∨
    (b.2=last ∧ 0<b.1 ∧ b.1<last ∧ b.1=p.1 ∧ b.2=p.2+2)

private theorem namesRim_inj {u : Nat} (v : View) (north x y : Interior (35+42*u))
    (z : Site u) (hx : NamesRim v north x z) (hy : NamesRim v north y z) : x=y := by
  unfold NamesRim at hx hy
  dsimp only at hx hy
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy
  all_goals try exact hx.1.trans hy.1.symm
  all_goals
    apply Subtype.ext
    apply point_inj v
    apply Prod.ext <;> omega

private theorem rimContact_wall {u h : Nat} (s : Window h (width h))
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) (p : Pos) :
    let B := prefixBox s (11+14*u) (3*s.length)
    EngineRimContact s (alongOffset s.axis B p) (acrossOffset s.axis B p) →
    ∃ b : Bool, (if b then B.south else B.east)=((35+42*u:Nat):Int)-1 ∧ B.Tooth p b := by
  have bounds := crop_bounds (11+14*u) rfl hk lo hi
  dsimp only
  intro contact
  cases dir : s.axis
  · simp [EngineRimContact,AcrossClosed,prefixBox,dir,alongOffset,acrossOffset,
      Window.length,Nat.cast_mul,Nat.cast_ofNat] at contact
    rcases contact with j|i
    · refine ⟨false,?_,?_⟩ <;>
        simp [SiteBox.Tooth,prefixBox,dir,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> omega
    · refine ⟨true,?_,?_⟩ <;>
        simp [SiteBox.Tooth,prefixBox,dir,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> omega
  · simp [EngineRimContact,AcrossClosed,prefixBox,dir,alongOffset,acrossOffset,
      Window.length,Nat.cast_mul,Nat.cast_ofNat] at contact
    rcases contact with j|i
    · refine ⟨true,?_,?_⟩ <;>
        simp [SiteBox.Tooth,prefixBox,dir,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> omega
    · refine ⟨false,?_,?_⟩ <;>
        simp [SiteBox.Tooth,prefixBox,dir,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> omega

/-- Wiring the marked rim contacts and the single north contact to the
engine's apex is acyclic. Any subset of the wires and any retained
interior edges are allowed, so this applies to scan prefixes as well.
The one-gap grounding argument uses the original forest throughout. -/
theorem axis_free_wired_acyclic {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : FanSlab.square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73)
    (I : SimpleGraph (Interior (35+42*u))) (sub : I ≤ interiorGraph F)
    (C : Finset (Interior (35+42*u))) :
    let k := 11+14*u
    let c := 1+3*(k-1)
    let R := firstRow k h
    let B := prefixBox s k (3*s.length)
    (∀ x∈C, x.val=railPoint u v c (R+1) ∨
      (x.val∈B.vertices v ∧ x.val∈F ∧ EngineRimContact s
        (alongOffset s.axis B (coordinates v x.val)) (acrossOffset s.axis B (coordinates v x.val)))) →
    (apexGraph I C).IsAcyclic := by
  classical
  let k := 11+14*u
  let c := 1+3*(k-1)
  let R := firstRow k h
  let B := prefixBox s k (3*s.length)
  have cl : 0<c := by dsimp [c,k]; omega
  have cu : c+1<35+42*u := by dsimp [c,k]; omega
  have last : R+2<35+42*u := by unfold R firstRow k; omega
  let north := railInner u v c (R+1) cl cu (by omega) (by omega)
  let N := north_attachment cl cu last (north_marked_edges line top)
  dsimp only
  intro contacts
  have build : ∀ x∈C, ∃ a : Attachment F x, NamesRim v north x a.rim.val := by
    intro x mem
    rcases contacts x mem with n|⟨inside,marked,contact⟩
    · have eq : x=north := Subtype.ext n
      subst x
      refine ⟨N,.inl ⟨rfl,?_⟩⟩
      change (coordinates v (railPoint u v c 0)).1=0
      rw [railPoint_coords (by omega : c<35+42*u) (by omega : 0<35+42*u)]
      rfl
    · obtain ⟨b,wall,tooth⟩ := rimContact_wall s hk lo hi _ contact
      let a : B.vertices v := ⟨x.val,inside⟩
      obtain ⟨A,label⟩ := rim_attachment H s hk lo hi (3*s.length) le_rfl b wall a marked tooth
      have eq : (⟨a.val,prefix_site_interior v s hk lo hi (3*s.length) le_rfl a⟩ :
          Interior (35+42*u))=x := Subtype.ext rfl
      cases eq
      refine ⟨A,?_⟩
      cases b
      · exact .inr (.inr label)
      · exact .inr (.inl label)
  choose A names using build
  exact apex_acyclic_of_attachments (by omega) F acy one I sub C A
    (fun x hx y hy eq => namesRim_inj v north x y (A x hx).rim.val (names x hx)
      (by rw [eq]; exact names y hy))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
