import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPhysicalCut

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 FanSeed

def alongOffset (axis : Axis) (B : SiteBox) (p : Pos) : Int :=
  match axis with
  | .horizontal => p.2-B.west
  | .vertical => p.1-B.north

def acrossOffset (axis : Axis) (B : SiteBox) (p : Pos) : Int :=
  match axis with
  | .horizontal => p.1-B.north
  | .vertical => p.2-B.west

def AcrossClosed {h : Nat} (s : Window h (width h)) : Prop :=
  s.start+s.depth = (match s.axis with | .horizontal => h | .vertical => width h)

/-- The base `rim` and the end-stage teeth in `Engine.advance`.
The independent north-root tooth is not part of this base mask. -/
def EngineRimContact {h : Nat} (s : Window h (width h)) (j i : Int) : Prop :=
  j+2=3*(s.length:Int) ∨ (AcrossClosed s ∧ i+2=3*(s.depth:Int))

/-- Open at the first site-line, the near transverse side, and the far
transverse side unless it is a true rim. The last site-line of an
unfinished scan is instead the retained frontier. -/
def EngineOpenSite {h : Nat} (s : Window h (width h)) (j i : Int) : Prop :=
  j=0 ∨ i=0 ∨ (¬AcrossClosed s ∧ i+1=3*(s.depth:Int))

theorem open_cut_engine_site {u h : Nat} (s : Window h (width h))
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) (p q : Pos) (side : Side) :
    let B := prefixBox s (11+14*u) used
    let last : Int := ((35+42*u:Nat):Int)-1
    let kind := CutKind s.axis (decide (used=3*s.length))
      (decide (B.south=last)) (decide (B.east=last))
    B.Crosses p q side → kind side≠2 →
    EngineOpenSite s (alongOffset s.axis B p) (acrossOffset s.axis B p) ∨
      (used<3*s.length ∧ alongOffset s.axis B p+1=used) := by
  have bounds := crop_bounds (11+14*u) rfl hk lo hi
  dsimp only
  intro hit notClosed
  cases dir : s.axis <;> cases side <;>
    simp [prefixBox,dir,SiteBox.Crosses,CutKind,EngineOpenSite,AcrossClosed,
      alongOffset,acrossOffset,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      at hit notClosed size ⊢ <;>
    (try split_ifs at notClosed) <;> omega

theorem engine_end_stage {length j : Nat} :
    j+2=3*length ↔ j/3+1=length ∧ j%3=1 := by omega

/-- The marked tooth reached in a closed-wall component lands on
precisely an engine rim contact, not on the unmarked outermost line. -/
theorem closed_tooth_engine_contact {u h : Nat} (s : Window h (width h))
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (south : Bool) (p : Pos) :
    let B := prefixBox s (11+14*u) used
    (if south then B.south else B.east)=((35+42*u:Nat):Int)-1 →
    B.Tooth p south →
    EngineRimContact s (alongOffset s.axis B p) (acrossOffset s.axis B p) := by
  have bounds := crop_bounds (11+14*u) rfl hk lo hi
  dsimp only
  intro wall atTooth
  cases dir : s.axis <;> cases south <;>
    simp [prefixBox,dir,SiteBox.Tooth,EngineRimContact,AcrossClosed,alongOffset,
      acrossOffset,Window.length,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at wall atTooth ⊢ <;> omega

/-- Soundness of the physical component test up to the partition
representation: a marked component has a real open side, a current
frontier, or an engine rim contact. -/
theorem cap_prefix_engine_hit {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) :
    let B := prefixBox s (11+14*u) used
    let last : Int := ((35+42*u:Nat):Int)-1
    let kind := CutKind s.axis (decide (used=3*s.length))
      (decide (B.south=last)) (decide (B.east=last))
    ∀ x : B.vertices v, x.val∈F →
      ∃ a : B.vertices v, ((Bonds F).induce (B.vertices v)).Reachable x a ∧
        ((∃ (b : Site u) (side : Side),
          B.Crosses (coordinates v a.val) (coordinates v b) side ∧ kind side≠2) ∨
        (a.val∈F ∧ EngineRimContact s
          (alongOffset s.axis B (coordinates v a.val)) (acrossOffset s.axis B (coordinates v a.val)))) := by
  dsimp only
  intro x mark
  rcases cap_prefix_component H acy score s hk lo hi used size x mark with
    ⟨a,b,side,spec,openCut,reached⟩|⟨a,south,wall,ma,tooth,reached⟩
  · exact ⟨a,reached,.inl ⟨b,side,spec,openCut⟩⟩
  · exact ⟨a,reached,.inr ⟨ma,closed_tooth_engine_contact s hk lo hi used south _ wall tooth⟩⟩

/-- Every marked component is accounted for by the flags used by the
strip scan. For a finished strip the frontier disjunct is impossible.
This does not assert that inserting all wires preserves acyclicity. -/
theorem cap_prefix_flags {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) :
    let B := prefixBox s (11+14*u) used
    ∀ x : B.vertices v, x.val∈F →
      ∃ a : B.vertices v, ((Bonds F).induce (B.vertices v)).Reachable x a ∧
        let j := alongOffset s.axis B (coordinates v a.val)
        let i := acrossOffset s.axis B (coordinates v a.val)
        EngineOpenSite s j i ∨ (used<3*s.length ∧ j+1=used) ∨
          (a.val∈F ∧ EngineRimContact s j i) := by
  dsimp only
  intro x mark
  obtain ⟨a,reached,hit⟩ := cap_prefix_engine_hit H acy score s hk lo hi used size x mark
  refine ⟨a,reached,?_⟩
  rcases hit with ⟨b,side,cross,openCut⟩|wired
  · exact (open_cut_engine_site s hk lo hi used size _ _ side cross openCut).elim Or.inl
      (fun front => .inr (.inl front))
  · exact .inr (.inr wired)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
