import GridGraphs.Accounting.BoundaryFiveEquality
import GridGraphs.Accounting.BoundarySix.Witnesses

/-! # Generic position of the fifth boundary hole -/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Without choosing any corner-hole orientations, the boundary holes are
four near-corner witnesses and one second-position vertex adjacent to a witness.
This locates the unique gap geometrically but does not transport `F` by symmetry. -/
theorem holes_eq_insert_second {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    ∃ (Q : Finset (GridVertex n n)) (u : GridVertex n n),
      Q.card = 4 ∧ u ∉ Q ∧
      (univ \ F).filter IsGridBoundary = insert u Q ∧
      (∀ q ∈ Q, BoundarySix.Near q) ∧ BoundarySix.Second u ∧
      ∃ q ∈ Q, (gridGraph n n).Adj u q := by
  classical
  obtain ⟨hcorners, hcard⟩ :=
    boundaryDeficiencySum_compl_eq_five_corners_and_card (by omega) F hacyc hb
  obtain ⟨Q, hQcard, hQU, hnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  let B := (univ \ F).filter IsGridBoundary
  have hBcard : B.card = 5 := hcard
  have hQB : Q ⊆ B := by
    intro q hq
    refine mem_filter.mpr ⟨hQU hq, ?_⟩
    have h := hnear q hq
    unfold BoundarySix.Near at h
    unfold IsGridBoundary
    omega
  obtain ⟨u, huB, huQ⟩ := exists_mem_notMem_of_card_lt_card
    (show Q.card < B.card by omega)
  have hB : B = insert u Q := by
    symm
    apply eq_of_subset_of_card_le (insert_subset huB hQB)
    rw [card_insert_of_notMem huQ, hQcard]
    exact hcard.le
  have hu : u ∉ F := (mem_sdiff.mp (mem_filter.mp huB).1).2
  have hub : IsGridBoundary u := (mem_filter.mp huB).2
  have hnc : ¬ BoundarySix.Corner u := fun h => hu (hcorners u h.1 h.2)
  have independent (x : GridVertex n n) (hx : x ∈ Q)
      (y : GridVertex n n) (hy : y ∈ Q) : ¬ (gridGraph n n).Adj x y := by
    have hxn := hnear x hx
    have hyn := hnear y hy
    simp only [gridGraph, adjacent, Fin.ext_iff]
    unfold BoundarySix.Near at hxn hyn
    omega
  have mem (v : GridVertex n n) (hv : v ∉ F) (hvb : IsGridBoundary v) :
      v = u ∨ v ∈ Q := by
    apply mem_insert.mp
    rw [← hB]
    exact mem_filter.mpr ⟨by simp [hv], hvb⟩
  obtain ⟨_, ⟨a, b, _, hab, ha, hb'⟩, _⟩ :=
    boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge (by omega) F hacyc hb
  have hex : ∃ q ∈ Q, (gridGraph n n).Adj u q := by
    rcases mem a ha hab.2.1 with rfl | haQ <;>
      rcases mem b hb' hab.2.2 with rfl | hbQ
    · exact (hab.1.ne rfl).elim
    · exact ⟨b, hbQ, hab.1⟩
    · exact ⟨a, haQ, hab.1.symm⟩
    · exact (independent a haQ b hbQ hab.1).elim
  obtain ⟨q, hq, huq⟩ := hex
  exact ⟨Q, u, hQcard, huQ, hB, hnear,
    (BoundarySix.neighbor_near hn hub (hnear q hq) huq).resolve_left hnc,
    q, hq, huq⟩

end GridGraphs.BoundaryFive
