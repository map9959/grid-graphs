import Mathlib

/-! # Finite-forest peeling with one isolated exceptional vertex -/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem reachable_from_isolate_eq {V : Type*} (H : SimpleGraph V) (w : V)
    (hiso : ∀ v, ¬ H.Adj w v) {x : V} (h : H.Reachable w x) : x = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons he _ => exact (hiso _ he).elim

/-- All vertices other than an isolate belong to the same component when
there are at most two components. Isolated vertices are not discarded. -/
theorem reachable_off_isolate {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hc : Nat.card H.ConnectedComponent ≤ 2) (w : V) (hiso : ∀ v, ¬ H.Adj w v)
    (x y : V) (hx : x ≠ w) (hy : y ≠ w) : H.Reachable x y := by
  classical
  have hwx : H.connectedComponentMk w ≠ H.connectedComponentMk x := by
    intro he
    exact hx (reachable_from_isolate_eq H w hiso (ConnectedComponent.eq.mp he))
  have hwy : H.connectedComponentMk w ≠ H.connectedComponentMk y := by
    intro he
    exact hy (reachable_from_isolate_eq H w hiso (ConnectedComponent.eq.mp he))
  by_contra hn
  have hxy : H.connectedComponentMk x ≠ H.connectedComponentMk y :=
    fun he => hn (ConnectedComponent.eq.mp he)
  let S : Finset H.ConnectedComponent :=
    {H.connectedComponentMk w, H.connectedComponentMk x, H.connectedComponentMk y}
  have hS : S.card = 3 := by simp [S, hwx, hwy, hxy]
  have h := card_le_card (subset_univ S)
  rw [hS, card_univ] at h
  rw [Nat.card_eq_fintype_card] at hc
  omega

theorem induced_walk_support_mem {V : Type*} (H : SimpleGraph V) (S : Set V)
    {x y : S} (p : (H.induce S).Walk x y) {v : V}
    (hv : v ∈ (p.map (Embedding.induce (G := H) S).toHom).support) : v ∈ S := by
  rw [Walk.support_map, List.mem_map] at hv
  obtain ⟨z, _, he⟩ := hv
  exact he ▸ z.2

/-- Two connected disjoint shores in a forest have at most one edge between
them. Both endpoints are unique; this also excludes two spokes at one root. -/
theorem forest_cross_edge_unique {V : Type*} (H : SimpleGraph V) (hacyc : H.IsAcyclic)
    (S T : Set V) (hdisj : Disjoint S T)
    (x y : S) (a b : T) (hxy : (H.induce S).Reachable x y)
    (hba : (H.induce T).Reachable b a)
    (hxa : H.Adj x.1 a.1) (hyb : H.Adj y.1 b.1) : x.1 = y.1 ∧ a.1 = b.1 := by
  classical
  obtain ⟨p⟩ := hxy
  obtain ⟨q⟩ := hba
  let p' := p.map (Embedding.induce (G := H) S).toHom
  let q' := q.map (Embedding.induce (G := H) T).toHom
  have hbridge := (isAcyclic_iff_forall_adj_isBridge.mp hacyc) hxa
  have he := (isBridge_iff_forall_walk_mem_edges.mp hbridge) (p'.append (.cons hyb q'))
  change s(x.1, a.1) ∈ (p'.append (.cons hyb q')).edges at he
  rw [Walk.edges_append] at he
  rcases List.mem_append.mp he with hp | he
  · have haS := induced_walk_support_mem H S p (p'.snd_mem_support_of_mem_edges hp)
    exact (Set.disjoint_left.mp hdisj haS a.2).elim
  · change s(x.1, a.1) ∈ s(y.1, b.1) :: q'.edges at he
    rcases List.mem_cons.mp he with he | hq
    · rcases Sym2.eq_iff.mp he with ⟨hxy, hab⟩ | ⟨hxb, _⟩
      · exact ⟨hxy, hab⟩
      · exact (Set.disjoint_left.mp hdisj (hxb ▸ x.2) b.2).elim
    · have hxT := induced_walk_support_mem H T q (q'.fst_mem_support_of_mem_edges hq)
      exact (Set.disjoint_left.mp hdisj x.2 hxT).elim

/-- The first exit of a walk supplies a crossing edge and an inner path to
its inner endpoint. No connectedness of the induced inner graph is assumed. -/
theorem first_exit {V : Type*} (H : SimpleGraph V) (S : Set V)
    {x y : V} (p : H.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ u : S, (H.induce S).Reachable ⟨x, hx⟩ u ∧ ∃ v, v ∉ S ∧ H.Adj u.1 v := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y he p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨u, hu, v, hv, huv⟩ := ih hz hy
      have he' : (H.induce S).Adj ⟨x, hx⟩ ⟨z, hz⟩ := he
      exact ⟨u, he'.reachable.trans hu, v, hv, huv⟩
    · exact ⟨⟨x, hx⟩, .rfl, z, hz, he⟩

end GridGraphs.BoundaryFive.Rootless
