import GridGraphs.ResidueZero.IncidenceGeometry

namespace GridGraphs.ResidueZero
open Finset

/-- The direction-weighted sum on a finite square vanishes if opposite
ports cancel and missing neighbours have zero contribution. -/
theorem sum_ports_zero (s : Nat) (f : Pos → Nat → Int)
    (missing : ∀ p∈siteSet s, ∀ d<4, ¬inside s (shift p d) → f p d=0)
    (paired : ∀ p∈siteSet s, ∀ d : Fin 2, inside s (shift p d) →
      f p d = -f (shift p d) (d.val+2)) :
    (∑ p ∈ siteSet s, ∑ d ∈ range 4, f p d) = 0 := by
  have opposite (d : Fin 2) :
      (∑ p ∈ siteSet s, f p d) = -(∑ p ∈ siteSet s, f p (d.val+2)) := by
    have h := sum_opposite (n:=s) d (fun _ q => -f q (d.val+2))
    calc
      _ = ∑ p ∈ siteSet s, if inside s (shift p d) then -f (shift p d) (d.val+2) else 0 := by
        apply sum_congr rfl; intro p hp; split
        · exact paired p hp d ‹_›
        · exact missing p hp _ (by have := d.isLt; omega) ‹_›
      _ = _ := by
        rw [h,←sum_neg_distrib]
        apply sum_congr rfl; intro p hp; split
        · rfl
        · rw [missing p hp _ (by have := d.isLt; omega) ‹_›,neg_zero]
  rw [sum_comm]
  simp only [show 4=3+1 by decide,sum_range_succ,sum_range_zero,zero_add]
  have h := opposite 0; have h' := opposite 1
  change (∑ p ∈ siteSet s, f p 0) = -(∑ p ∈ siteSet s, f p 2) at h
  change (∑ p ∈ siteSet s, f p 1) = -(∑ p ∈ siteSet s, f p 3) at h'
  linarith

/-- The covering-window loop on stars exactly pays the slot loop on
patches. Both loops use a common physical price; no estimate is needed. -/
theorem sum_cover_slots (n : Nat) (cover slot : Pos → Nat → Int)
    (missing : ∀ p∈siteSet n, ∀ q : Fin 9, ¬inside (n-2:Nat) (p-offset q) → cover p q=0)
    (paired : ∀ a∈siteSet (n-2), ∀ q : Fin 9, cover (a+offset q) q = slot a q) :
    (∑ p ∈ siteSet n, ∑ q ∈ range 9, cover p q) =
    ∑ a ∈ siteSet (n-2), ∑ q ∈ range 9, slot a q := by
  rw [sum_comm, sum_comm (s:=siteSet (n-2))]
  apply sum_congr rfl; intro j hj
  let q : Fin 9 := ⟨j,mem_range.mp hj⟩
  have h := sum_offsets (n:=n) q (fun _ p => cover p j)
  calc
    _ = ∑ p ∈ siteSet n, if inside (n-2:Nat) (p-offset q) then cover p j else 0 := by
      apply sum_congr rfl; intro p hp; split
      · rfl
      · exact missing p hp q ‹_›
    _ = _ := h.trans (sum_congr rfl (fun a ha => paired a ha q))

end GridGraphs.ResidueZero
