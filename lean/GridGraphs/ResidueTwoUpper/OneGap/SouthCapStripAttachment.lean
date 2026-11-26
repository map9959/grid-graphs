import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripContraction
import GridGraphs.ResidueTwoUpper.OneGap.Grounding

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 FanSeed Camera BoundarySix.Connected SimpleGraph

abbrev Interior (n : Nat) := {x : GridVertex n n // ¬ IsGridBoundary x}
abbrev interiorGraph {n} (F : Finset (GridVertex n n)) :=
  (Bonds F).induce {x | ¬ IsGridBoundary x}

theorem boundary_in_view {n : Nat} (v : View) (x : GridVertex n n) :
    IsGridBoundary x ↔
      (coordinates v x).1=0 ∨ (coordinates v x).1+1=n ∨
      (coordinates v x).2=0 ∨ (coordinates v x).2+1=n := by
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [IsGridBoundary,coordinates,coord,reflect] <;> omega

theorem prefix_site_interior {u h : Nat} (v : View) (s : Window h (width h))
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43) (used : Nat) (size : used≤3*s.length)
    (x : (prefixBox s (11+14*u) used).vertices (n:=35+42*u) v) : ¬IsGridBoundary x.val := by
  rw [boundary_in_view v]
  have b := prefix_bounds s hk lo hi size
  have m := x.2
  change SiteBox.Contains _ _ at m
  unfold SiteBox.Contains at m
  obtain ⟨a,b,c,d⟩ := b
  omega

/-- Naming an attachment by its actual perimeter vertex, and not by
a fresh local arrow, lets one-gap grounding compare different strips. -/
structure Attachment {n : Nat} (F : Finset (GridVertex n n)) (x : Interior n) where
  inside : Interior n
  rim : PerimeterVertex n
  reached : (interiorGraph F).Reachable x inside
  link : (Bonds F).Adj inside.val rim.val

/-- If distinct wired vertices have different actual perimeter
attachments then adding the engine's common root is sound. The
paths to the perimeter may share edges with retained pendant limbs. -/
theorem apex_acyclic_of_attachments {n : Nat} (hn : 3≤n) (F : Finset (GridVertex n n))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (I : SimpleGraph (Interior n)) (sub : I ≤ interiorGraph F)
    (C : Finset (Interior n)) (A : ∀ x∈C, Attachment F x)
    (distinct : ∀ x (hx : x∈C) y (hy : y∈C), (A x hx).rim=(A y hy).rim → x=y) :
    (apexGraph I C).IsAcyclic := by
  apply apex_acyclic ((acy.induce _).anti sub)
  intro x hx y hy no r
  let a := A x hx
  let b := A y hy
  have path := a.reached.symm.trans ((r.mono sub).trans b.reached)
  exact no (distinct x hx y hy (unique_attachment hn F acy one a.inside b.inside
    a.rim b.rim path a.link b.link).2)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
