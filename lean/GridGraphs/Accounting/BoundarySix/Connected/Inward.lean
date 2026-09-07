import GridGraphs.Accounting.BoundarySix.Balance
import GridGraphs.Accounting.CarrierLayers.FourCarrier.DeepExtension

/-! # Physical inward constraints with one forced component

With no shallow carriers, the sole possible preserved next-ring vertex cannot
be a next-ring corner. A missing outer spoke must be supplied from depth two,
except at the two lateral neighbors of that sole next-ring vertex.
These are necessary geometric conditions, not a short-carrier existence claim.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier

/-- A depth-one vertex at either end of a side would extend to a second
next-ring vertex. Thus neither next-ring corner can be preserved. -/
theorem inward_position_bounds {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    2 ≤ t.val ∧ t.val + 3 ≤ n := by
  have hz := inward_depth_two_of_no_shallow (by omega) F hacyc hzero s t ht hw
  have hwR : IsNextRing (sideChart s (t, ⟨1, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, IsNextRing] <;> omega
  by_contra h
  have hzR : IsNextRing (sideChart s (t, ⟨2, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, IsNextRing] <;> omega
  have he := sideChart_injective s
    (boundaryDeficiencySum_compl_eq_six_next_ring_unique hn F hacyc hb hw hz hwR hzR)
  have hd := congrArg (fun v : GridVertex n n => v.2.val) he
  change 1 = 2 at hd
  omega

/-- The two diagonal outer vertices of any preserved inward vertex are holes.
The proof uses actual unit cells in the side chart. -/
theorem inward_diagonal_holes {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (t : Nat) (ht : 0 < t) (htn : t + 1 < n)
    (hw : sideChart s (⟨t, by omega⟩, ⟨1, by omega⟩) ∈ F) :
    sideChart s (⟨t - 1, by omega⟩, ⟨0, by omega⟩) ∉ F ∧
      sideChart s (⟨t + 1, htn⟩, ⟨0, by omega⟩) ∉ F := by
  have hac := sideChart_acyclic s F hacyc
  have hleft := grid_cell_has_unforced_edge
    (⟨t - 1, by omega⟩ : Fin (n - 1)) (⟨0, by omega⟩ : Fin (n - 1)) hac
  have hright := grid_cell_has_unforced_edge
    (⟨t, by omega⟩ : Fin (n - 1)) (⟨0, by omega⟩ : Fin (n - 1)) hac
  have he : t - 1 + 1 = t := by omega
  simp only [cell00, cell01, cell11, cell10, Set.mem_ofPred_eq, he] at hleft hright
  constructor
  · rcases hleft with h | h | h | h
    · exact h.1
    · exact (h.2 hw).elim
    · exact (h.1 hw).elim
    · exact h.2
  · rcases hright with h | h | h | h
    · exact (h.2 hw).elim
    · exact (h.1 hw).elim
    · exact h.2
    · exact h.1

/-- Domination of a missing outer spoke forces depth two, unless a lateral
next-ring neighbor is preserved. No presumed annulus connectivity is used. -/
theorem hole_deep_or_lateral {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Nat) (ht : 2 ≤ t) (htn : t + 3 ≤ n)
    (hhole : sideChart s (⟨t, by omega⟩, ⟨0, by omega⟩) ∉ F) :
    sideChart s (⟨t, by omega⟩, ⟨2, by omega⟩) ∈ F ∨
      sideChart s (⟨t - 1, by omega⟩, ⟨1, by omega⟩) ∈ F ∨
      sideChart s (⟨t + 1, by omega⟩, ⟨1, by omega⟩) ∈ F := by
  by_cases hw : sideChart s (⟨t, by omega⟩, ⟨1, by omega⟩) ∈ F
  · exact Or.inl (inward_depth_two_of_no_shallow hn F hacyc hzero s
      ⟨t, by omega⟩ (by dsimp; omega) hw)
  obtain ⟨v, hv, hadj⟩ := preserved_neighbor_of_one_forced_component (by omega) F hc _ hw
  obtain ⟨w, rfl⟩ := sideChart_surjective s v
  have hadj' := (sideChart_adj s _ _).mp hadj
  have hcases : w = (⟨t, by omega⟩, ⟨0, by omega⟩) ∨
      w = (⟨t, by omega⟩, ⟨2, by omega⟩) ∨
      w = (⟨t - 1, by omega⟩, ⟨1, by omega⟩) ∨
      w = (⟨t + 1, by omega⟩, ⟨1, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
    simp only [Prod.ext_iff, Fin.ext_iff]
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (hhole hv).elim
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv)

/-- Every exception to depth-two domination is immediately beside the unique
preserved next-ring vertex. This quantifies over all four sides simultaneously. -/
theorem missing_deep_locates_unique_ring {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Nat) (ht : 2 ≤ t) (htn : t + 3 ≤ n)
    (hhole : sideChart s (⟨t, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (hdeep : sideChart s (⟨t, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∃ q : Fin n, (q.val + 1 = t ∨ t + 1 = q.val) ∧
      2 ≤ q.val ∧ q.val + 3 ≤ n ∧
      sideChart s (q, ⟨1, by omega⟩) ∈ F ∧
      ∀ v ∈ F, IsNextRing v → v = sideChart s (q, ⟨1, by omega⟩) := by
  have h := (hole_deep_or_lateral (by omega) F hacyc hc hzero s t ht htn hhole).resolve_left hdeep
  have finish (q : Fin n) (hq : q.val + 1 = t ∨ t + 1 = q.val)
      (hqF : sideChart s (q, ⟨1, by omega⟩) ∈ F) :
      2 ≤ q.val ∧ q.val + 3 ≤ n ∧
      sideChart s (q, ⟨1, by omega⟩) ∈ F ∧
      ∀ v ∈ F, IsNextRing v → v = sideChart s (q, ⟨1, by omega⟩) := by
    have hqt : 0 < q.val ∧ q.val + 1 < n := by omega
    have hbounds := inward_position_bounds hn F hacyc hb hzero s q hqt hqF
    refine ⟨hbounds.1, hbounds.2, hqF, ?_⟩
    intro v hv hvR
    apply boundaryDeficiencySum_compl_eq_six_next_ring_unique hn F hacyc hb hv hqF hvR
    fin_cases s <;> simp [sideChart, IsNextRing] <;> omega
  rcases h with h | h
  · exact ⟨⟨t - 1, by omega⟩, Or.inl (by dsimp; omega),
      finish _ (Or.inl (by dsimp; omega)) h⟩
  · exact ⟨⟨t + 1, by omega⟩, Or.inr rfl, finish _ (Or.inr rfl) h⟩

end GridGraphs.BoundarySix.Connected
