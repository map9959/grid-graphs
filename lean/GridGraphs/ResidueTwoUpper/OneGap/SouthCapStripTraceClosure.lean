import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripTrace

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph ResidueZero FanSeed

/-- Readout obligations for one graph of a physical prefix. A marked
engine vertex reachable from an old slot must come from an actual
mark. Open and wired flags are interpreted in the whole processed
graph, not in the graph induced just on surviving slots. -/
structure PrefixReadout {V : Type} {u h n : Nat} {F : Finset (Site u)} {v}
    (s : Window h (width h)) (used : Nat)
    (G : SimpleGraph V) (f : Fin (n+1+n) → V) (mark openSite : V → Prop) where
  point : (prefixBox s (11+14*u) used).vertices v → V
  reach : ∀ x y, ((Bonds F).induce ((prefixBox s (11+14*u) used).vertices v)).Reachable x y →
    G.Reachable (point x) (point y)
  marks : ∀ x ∈ Row.drop n, ∀ z, G.Reachable (f x) z → mark z →
    ∃ a, a.val∈F ∧ point a=z
  openFlag : ∀ a,
    let B := prefixBox s (11+14*u) used
    EngineOpenSite s (alongOffset s.axis B (coordinates v a.val))
      (acrossOffset s.axis B (coordinates v a.val)) → ComponentFlag G openSite (point a)
  frontier : ∀ a,
    let B := prefixBox s (11+14*u) used
    used < 3*s.length → alongOffset s.axis B (coordinates v a.val)+1=used →
    ∃ i, f (Row.keep i)=point a
  wiredFlag : ∀ a,
    let B := prefixBox s (11+14*u) used
    a.val∈F → EngineRimContact s (alongOffset s.axis B (coordinates v a.val))
      (acrossOffset s.axis B (coordinates v a.val)) → ComponentFlag G openSite (point a)

/-- The physical cut theorem discharges the disappearing-component
test of a row with the stated readout. There is no axis filter and a
component that leaves via an unmarked endpoint is still accounted for. -/
theorem physical_row_closure {V : Type} {u h n : Nat} {F : Finset (Site u)} {v q dir}
    (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) {G : SimpleGraph V} {f : Fin (n+1+n) → V}
    {mark openSite : V → Prop} (readout : PrefixReadout (F:=F) (v:=v) s used G f mark openSite) :
    RowClosure G f mark openSite (Row.drop n) Row.keep := by
  intro x old hasMark
  obtain ⟨z,xz,mz⟩ := hasMark
  obtain ⟨a,ma,az⟩ := readout.marks x old z xz mz
  obtain ⟨b,ab,supported⟩ := cap_prefix_flags H acy score s hk lo hi used size a ma
  have xb := xz.trans (az ▸ readout.reach a b ab)
  rcases supported with open'|⟨unfinished,atFront⟩|⟨mb,contact⟩
  · obtain ⟨e,r,flag⟩ := readout.openFlag b open'
    exact .inl ⟨e,xb.trans r,flag⟩
  · obtain ⟨i,same⟩ := readout.frontier b unfinished atFront
    exact .inr ⟨i,same ▸ xb.symm⟩
  · obtain ⟨e,r,flag⟩ := readout.wiredFlag b mb contact
    exact .inl ⟨e,xb.trans r,flag⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
