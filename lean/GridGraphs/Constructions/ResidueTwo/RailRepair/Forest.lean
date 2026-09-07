import GridGraphs.Constructions.ResidueTwo.RailRepair.Geometry

/-! # Uniform support gluing for the terminal-rail repair -/

namespace GridGraphs.RailRepair

open Finset SimpleGraph BoundaryFiveConstruction BoundaryFiveFrame
open ResidueTwoStaircase (Vertex)

noncomputable section
attribute [local instance] Classical.propDecidable

theorem support_biUnion {s : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Finset (Vertex s)) (v : Vertex s) :
    v ∈ (J (S.biUnion p)).support ↔ ∃ i ∈ S, v ∈ (J (p i)).support := by
  constructor
  · rintro ⟨w, hw⟩
    change (J (S.biUnion p)).Adj v w at hw
    rcases hw with ⟨ha, hv | hw⟩
    · obtain ⟨i, hi, hv⟩ := mem_biUnion.mp hv
      exact ⟨i, hi, w, ha, Or.inl hv⟩
    · obtain ⟨i, hi, hw⟩ := mem_biUnion.mp hw
      exact ⟨i, hi, w, ha, Or.inr hw⟩
  · rintro ⟨i, hi, w, hw⟩
    change (J (p i)).Adj v w at hw
    refine ⟨w, hw.1, ?_⟩
    rcases hw.2 with hv | hw
    · exact Or.inl (mem_biUnion.mpr ⟨i, hi, hv⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨i, hi, hw⟩)

def baseGraph (s : ℕ) : SimpleGraph (Vertex s) := Houter (3 * s + 5) ⊔ J (base s)

theorem baseGraph_isAcyclic {s : ℕ} (hs : 2 ≤ s) : (baseGraph s).IsAcyclic := by
  have h := ResidueTwoStaircase.Ffull_isAcyclic hs
  rw [forcedEdgeGraph_Ffull] at h
  apply IsAcyclic.anti (h := h)
  apply sup_le_sup_left
  exact forcedEdgeGraph_mono _ (base_subset_source s)

theorem new_baseGraph_inter_location {s : ℕ} (hs : 2 ≤ s) (i : NewIndex s)
    {v : Vertex s} (hi : v ∈ newFootprint s i) (hv : v ∈ (baseGraph s).support) :
    Attachment s i v := by
  rcases (support_sup _ _ ▸ hv) with hf | hb
  · exact new_frame_inter_location hs i hi hf
  · obtain ⟨j, _, hj⟩ := (support_biUnion univ (basePiece s) v).mp hb
    exact new_base_inter_location hs i j hi (base_support_subset s j hj)

def familyGraph (s : ℕ) (S : Finset (NewIndex s)) : SimpleGraph (Vertex s) :=
  baseGraph s ⊔ J (S.biUnion (newPiece s))

theorem familyGraph_insert (s : ℕ) (S : Finset (NewIndex s)) (i : NewIndex s) :
    familyGraph s (insert i S) = J (newPiece s i) ⊔ familyGraph s S := by
  ext v w
  simp only [familyGraph, J, sup_adj, forcedEdgeGraph, biUnion_insert, mem_coe, mem_union]
  tauto

/-- Arbitrary subsets of the new motifs can be glued, in any order. -/
theorem familyGraph_isAcyclic {s : ℕ} (hs : 2 ≤ s) (S : Finset (NewIndex s)) :
    (familyGraph s S).IsAcyclic := by
  induction S using Finset.induction_on with
  | empty =>
      have he : familyGraph s ∅ = baseGraph s := by
        ext v w
        simp [familyGraph, J, forcedEdgeGraph]
      rw [he]
      exact baseGraph_isAcyclic hs
  | @insert i S hi ih =>
      rw [familyGraph_insert]
      apply (new_isAcyclic s i).sup_of_support_inter_subsingleton ih
      have location {v : Vertex s}
          (hv : v ∈ (J (newPiece s i)).support ∩ (familyGraph s S).support) :
          Attachment s i v := by
        have hp := new_support_subset s i hv.1
        rcases (support_sup _ _ ▸ hv.2) with hb | hn
        · exact new_baseGraph_inter_location hs i hp hb
        · obtain ⟨j, hj, hvj⟩ := (support_biUnion S (newPiece s) v).mp hn
          have hne : i ≠ j := by intro he; exact hi (he ▸ hj)
          exact False.elim (Set.disjoint_left.mp (new_footprints_disjoint hs hne)
            hp (new_support_subset s j hvj))
      intro v hv w hw
      exact attachment_subsingleton s i (location hv) (location hw)

/-- The actual repaired center set forces a forest on all `(3s+5)^2` vertices. -/
theorem Ffull_isAcyclic {s : ℕ} (hs : 2 ≤ s) :
    (forcedEdgeGraph (gridGraph (3 * s + 5) (3 * s + 5))
      (↑(Ffull (repaired s)) : Set (Vertex s))).IsAcyclic := by
  rw [forcedEdgeGraph_Ffull]
  have he : Houter (3 * s + 5) ⊔ J (repaired s) = familyGraph s univ := by
    ext v w
    simp only [familyGraph, baseGraph, repaired, J, forcedEdgeGraph, sup_adj,
      mem_coe, mem_union]
    tauto
  rw [he]
  exact familyGraph_isAcyclic hs univ

end
end GridGraphs.RailRepair
