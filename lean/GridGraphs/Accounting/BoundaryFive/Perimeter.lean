import GridGraphs.Constructions.BoundaryFive.BoundaryFiveFrame

/-! # The actual perimeter after positioning only the unique gap

The rank parametrization is borrowed from the concrete frame, but no equality
with its preserved set or its spokes is assumed. Every edge below is proved
present in the forced graph of the supplied set `F`.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph BoundaryFiveFrame

/-- Positioning the gap suffices for connectivity of the actual forced
perimeter. The other three corner-hole orientations are unrestricted. -/
theorem perimeter_preconnected_of_top_gap {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hb' : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce
      {v | IsGridBoundary v}).Preconnected := by
  classical
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨2, by omega⟩)
  obtain ⟨e, _, he⟩ := boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge
    (by omega) F hacyc hb
  have hab : IsPerimeterEdge n a b := by
    simp [IsPerimeterEdge, IsBoundaryVertex, gridGraph, adjacent, a, b]
  have heab : s(a, b) = e := he a b hab ha hb'
  have edge {x y : GridVertex n n} (hx : IsGridBoundary x) (hy : IsGridBoundary y)
      (hrank : boundaryRank x + 1 = boundaryRank y ∨
        boundaryRank y + 1 = boundaryRank x) :
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj x y := by
    have hcanonical := (boundary_adj_iff_rank hn hx hy).mpr hrank
    refine ⟨hcanonical.1, ?_⟩
    by_contra h
    have hxf : x ∉ F := fun hxf => h (Or.inl hxf)
    have hyf : y ∉ F := fun hyf => h (Or.inr hyf)
    have heq := (he x y ⟨hcanonical.1, hx, hy⟩ hxf hyf).trans heab.symm
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [boundaryRank, a, b] at hrank <;> omega
  let S := (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce
    {v | IsGridBoundary v}
  have hbb : IsGridBoundary b := Or.inl rfl
  let root : {v : GridVertex n n | IsGridBoundary v} := ⟨b, hbb⟩
  have hbrank : boundaryRank b = 0 := by simp [boundaryRank, b]
  have reach : ∀ k, ∀ (v : GridVertex n n) (hv : IsGridBoundary v),
      boundaryRank v = k → S.Reachable root ⟨v, hv⟩ := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      have hev := boundaryRank_injective hn hv hbb (hk.trans hbrank.symm)
      have he' : (⟨v, hv⟩ : {v : GridVertex n n | IsGridBoundary v}) = root :=
        Subtype.ext hev
      rw [he']
    | succ k ih =>
      intro v hv hk
      have hbound := boundaryRank_lt hn v hv
      obtain ⟨p, hp, hpk⟩ := exists_boundaryRank hn k (by omega)
      have hadj : S.Adj ⟨p, hp⟩ ⟨v, hv⟩ :=
        edge (x := p) (y := v) hp hv (Or.inl (by omega))
      exact (ih p hp hpk).trans hadj.reachable
  intro x y
  exact (reach _ x.1 x.2 rfl).symm.trans (reach _ y.1 y.2 rfl)

end GridGraphs.BoundaryFive
