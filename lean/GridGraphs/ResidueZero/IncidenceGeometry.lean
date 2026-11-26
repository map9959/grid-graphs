import GridGraphs.ResidueZero.Normalization

namespace GridGraphs.ResidueZero
open Finset

/-- The upper endpoint of a lattice edge in a square view. -/
theorem image_step (n : Int) (g : Fin 8) (d : Fin 4) (p : Pos) :
    image n g (shift p d) = shift (image n g p) (turn g d) := by
  fin_cases g <;> fin_cases d <;> ext <;> simp [image,shift,turn] <;> ring

/-- Rotating a patch rotates both its origin (in the smaller square) and
the offset of each site (in the 3×3 square). -/
theorem image_offset (n : Int) (g : Fin 8) (p u : Pos) :
    image n g (p+u) = image (n-2) g p + image 3 g u := by
  fin_cases g <;> ext <;> simp [image] <;> ring

def siteSet (n : Nat) : Finset Pos := univ.image (coord (n:=n))
theorem mem_siteSet {n : Nat} {p : Pos} : p∈siteSet n ↔ inside n p := by
  constructor
  · intro h; obtain ⟨v,_,rfl⟩ := mem_image.mp h; exact coord_inside v
  · intro h
    simp [inside] at h
    refine mem_image.mpr ⟨(⟨p.1.toNat,by omega⟩,⟨p.2.toNat,by omega⟩),mem_univ _,?_⟩
    ext <;> simp [coord] <;> omega

theorem physical_sum (n : Nat) (f : Pos → Int) :
    (∑ p ∈ siteSet n, f p) = ∑ v : GridVertex n n, f (coord v) :=
  Finset.sum_image (fun _ _ _ _ e => coord_injective e)

theorem reverse_step (p : Pos) (d : Fin 2) : shift (shift p d) (d.val+2)=p ∧
    shift (shift p (d.val+2)) d=p := by
  fin_cases d <;> simp [shift]

/-- The positive directed incidences can be summed from either endpoint.
The price can depend on both physical positions and any shared event. -/
theorem sum_opposite {n : Nat} (d : Fin 2) (f : Pos → Pos → Int) :
    (∑ p ∈ siteSet n, if inside n (shift p d) then f p (shift p d) else 0) =
    ∑ q ∈ siteSet n, if inside n (shift q (d.val+2)) then f (shift q (d.val+2)) q else 0 := by
  rw [←sum_filter,←sum_filter]
  apply sum_bij' (fun p _ => shift p d) (fun q _ => shift q (d.val+2))
  · intro p hp
    obtain ⟨a,b⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_siteSet.mpr b,by simpa [(reverse_step p d).1] using mem_siteSet.mp a⟩
  · intro p hp
    obtain ⟨a,b⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_siteSet.mpr b,by simpa [(reverse_step p d).2] using mem_siteSet.mp a⟩
  · exact fun p _ => (reverse_step p d).1
  · exact fun p _ => (reverse_step p d).2
  · intro p _; simp [(reverse_step p d).1]

/-- Enumerating patches containing a given site is the transpose of
enumerating the nine sites of each patch. -/
theorem sum_offsets {n : Nat} (q : Fin 9) (f : Pos → Pos → Int) :
    (∑ p ∈ siteSet n, if inside (n-2:Nat) (p-offset q) then f (p-offset q) p else 0) =
    ∑ a ∈ siteSet (n-2), f a (a+offset q) := by
  rw [←sum_filter]
  apply sum_bij' (fun p _ => p-offset q) (fun a _ => a+offset q)
  · intro p hp; exact mem_siteSet.mpr (mem_filter.mp hp).2
  · intro a ha
    have h := mem_siteSet.mp ha
    apply mem_filter.mpr
    refine ⟨mem_siteSet.mpr ?_,by simpa using h⟩
    change inside n (a.1+(q.val/3:Nat),a.2+(q.val%3:Nat))
    simp [inside] at h ⊢
    have := q.isLt; omega
  · intro p _; simp
  · intro a _; simp
  · intro p _; simp

end GridGraphs.ResidueZero
