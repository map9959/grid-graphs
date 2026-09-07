import GridGraphs.Accounting.BoundarySix.Connected.RingCycle
import GridGraphs.Accounting.BoundaryFive.Rootless.Geometry
import GridGraphs.Surgery.GridCrop

/-! # Actual deep roots below a connected annulus

The offset crop retains every deep vertex, including unpreserved vertices.
No shallow carriers ensures that every forced crossing has a preserved deep
endpoint. Ambient connectivity supplies roots; annulus connectivity and the
physical forest forbid two distinct roots in the same deep forced component.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

def deepEmbedding {m n : Nat} (hm : m + 4 = n) : GridVertex m m ↪ GridVertex n n :=
  gridOffsetEmbedding 2 2 (by omega) (by omega)

noncomputable def deepSelected {m n : Nat} (hm : m + 4 = n)
    (F : Finset (GridVertex n n)) : Finset (GridVertex m m) :=
  univ.filter (fun v => deepEmbedding hm v ∈ F)

@[simp] theorem mem_deepSelected {m n : Nat} (hm : m + 4 = n)
    (F : Finset (GridVertex n n)) (v : GridVertex m m) :
    v ∈ deepSelected hm F ↔ deepEmbedding hm v ∈ F := by simp [deepSelected]

theorem deepEmbedding_not_mem {m n : Nat} (hm : m + 4 = n) (v : GridVertex m m) :
    ¬ Mem (deepEmbedding hm v) := by
  simp only [deepEmbedding, Mem, gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val]
  omega

theorem deepEmbedding_range {m n : Nat} (hm : m + 4 = n) {v : GridVertex n n}
    (hv : ¬ Mem v) : ∃ w, deepEmbedding hm w = v := by
  unfold Mem at hv
  refine ⟨(⟨v.1.val - 2, by omega⟩, ⟨v.2.val - 2, by omega⟩), ?_⟩
  apply Prod.ext <;> apply Fin.ext <;> simp [deepEmbedding] <;> omega

theorem deepSelected_acyclic {m n : Nat} (hm : m + 4 = n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (forcedEdgeGraph (gridGraph m m) (↑(deepSelected hm F) : Set _)).IsAcyclic := by
  have he : (↑(deepSelected hm F) : Set _) = deepEmbedding hm ⁻¹' (↑F : Set _) := by
    ext v
    simp
  rw [he]
  exact forcedEdgeGraph_gridOffsetEmbedding_isAcyclic 2 2 _ _ _ hacyc

private theorem crossing_chart {n : Nat} (hn : 5 ≤ n) {a z : GridVertex n n}
    (ha : Mem a) (hz : ¬ Mem z) (hadj : (gridGraph n n).Adj a z) :
    ∃ (s : Fin 4) (t : Fin n), (0 < t.val ∧ t.val + 1 < n) ∧
      a = sideChart s (t, ⟨1, by omega⟩) ∧ z = sideChart s (t, ⟨2, by omega⟩) := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
  unfold Mem at ha hz
  rcases ha with ha | ha | ha | ha
  · refine ⟨0, z.2, by omega, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [sideChart] <;> omega
  · refine ⟨1, z.2, by omega, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [sideChart] <;> omega
  · refine ⟨2, z.1, by omega, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [sideChart] <;> omega
  · refine ⟨3, z.1, by omega, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [sideChart] <;> omega

/-- Every forced edge crossing from the annulus has a preserved deep endpoint
when shallow carriers are absent. -/
theorem crossing_deep_preserved {m n : Nat} (hm : m + 4 = n) (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0)
    (v : GridVertex m m) {a : GridVertex n n} (ha : Mem a)
    (h : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbedding hm v) a) :
    v ∈ deepSelected hm F ∧ IsGridBoundary v := by
  have hF : deepEmbedding hm v ∈ F := by
    rcases h.2 with hv | haF
    · exact hv
    · obtain ⟨s, t, ht, heA, heD⟩ := crossing_chart hn ha (deepEmbedding_not_mem hm v) h.1.symm
      rw [heA] at haF
      rw [heD]
      exact inward_depth_two_of_no_shallow hn F hacyc hzero s t ht haF
  refine ⟨(mem_deepSelected hm F v).mpr hF, ?_⟩
  have hadj := h.1
  simp only [gridGraph, adjacent, Fin.ext_iff, deepEmbedding,
    gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val] at hadj
  unfold Mem at ha
  unfold IsGridBoundary
  omega

private def deepHom {m n : Nat} (hm : m + 4 = n) (F : Finset (GridVertex n n)) :
    forcedEdgeGraph (gridGraph m m) (↑(deepSelected hm F) : Set _) →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
  { toFun := deepEmbedding hm
    map_rel' := by
      intro v w h
      exact ⟨(gridOffsetEmbedding_adj_iff 2 2 _ _ v w).mpr h.1,
        h.2.elim (fun hv => Or.inl ((mem_deepSelected hm F v).mp hv))
          (fun hw => Or.inr ((mem_deepSelected hm F w).mp hw))⟩ }

/-- Ambient connectivity roots every actual deep forced component, including
any putative isolate. No annulus connectivity is needed for existence. -/
theorem deep_boundary_rooted {m n : Nat} (hm : m + 4 = n) (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (hzero : (nextRingCarriers F).card = 0) :
    BoundaryFive.Rootless.BoundaryRooted (m := m) (↑(deepSelected hm F) : Set _) := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let D := forcedEdgeGraph (gridGraph m m) (↑(deepSelected hm F) : Set _)
  have go {x y : GridVertex n n} (p : H.Walk x y) : Mem y →
      ∀ v, deepEmbedding hm v = x → ∃ u ∈ deepSelected hm F, IsGridBoundary u ∧ D.Reachable v u := by
    induction p with
    | nil =>
      intro hy v he
      exact (deepEmbedding_not_mem hm v (he ▸ hy)).elim
    | @cons x z y hadj p ih =>
      intro hy v he
      subst x
      by_cases hz : Mem z
      · obtain ⟨hvF, hvb⟩ := crossing_deep_preserved hm hn F hacyc hzero v hz hadj
        exact ⟨v, hvF, hvb, .refl v⟩
      · obtain ⟨w, hw⟩ := deepEmbedding_range hm hz
        obtain ⟨u, hu, hub, hreach⟩ := ih hy w hw
        have hsmall : D.Adj v w := by
          rw [← hw] at hadj
          refine ⟨(gridOffsetEmbedding_adj_iff 2 2 _ _ v w).mp hadj.1, ?_⟩
          simpa only [mem_coe, mem_deepSelected] using hadj.2
        exact ⟨u, hu, hub, hsmall.reachable.trans hreach⟩
  have : Subsingleton H.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hc.le
  intro v
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hreach : H.Reachable (deepEmbedding hm v) a :=
    ConnectedComponent.exact (Subsingleton.elim _ _)
  obtain ⟨p⟩ := hreach
  exact go p (by simp [a, Mem]) v rfl

private theorem boundary_attachment {m n : Nat} (hm : m + 4 = n)
    (v : GridVertex m m) (hv : IsGridBoundary v) :
    ∃ a : GridVertex n n, Mem a ∧ (gridGraph n n).Adj a (deepEmbedding hm v) := by
  let z := deepEmbedding hm v
  rcases hv with hv | hv | hv | hv
  · refine ⟨(⟨1, by omega⟩, z.2), Or.inl (by simp), ?_⟩
    simp [gridGraph, adjacent, Fin.ext_iff, z, deepEmbedding, hv]
  · refine ⟨(⟨n - 2, by omega⟩, z.2), Or.inr (Or.inl (by simp; omega)), ?_⟩
    simp [gridGraph, adjacent, Fin.ext_iff, z, deepEmbedding]
    omega
  · refine ⟨(z.1, ⟨1, by omega⟩), Or.inr (Or.inr (Or.inl (by simp))), ?_⟩
    simp [gridGraph, adjacent, Fin.ext_iff, z, deepEmbedding, hv]
  · refine ⟨(z.1, ⟨n - 2, by omega⟩), Or.inr (Or.inr (Or.inr (by simp; omega))), ?_⟩
    simp [gridGraph, adjacent, Fin.ext_iff, z, deepEmbedding]
    omega

/-- The unique path in the ambient forest forbids two preserved boundary
roots in one actual deep forced component. -/
theorem deep_unique_boundary_roots {m n : Nat} (hm : m + 4 = n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcA : Fintype.card (forcedEdgeGraph (graph n)
      (↑(selected F) : Set _)).ConnectedComponent = 1) :
    BoundaryFive.Rootless.UniqueBoundaryRoots (m := m) (↑(deepSelected hm F) : Set _) := by
  intro u hu v hv hub hvb hreach
  by_contra hne
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let A := forcedEdgeGraph (graph n) (↑(selected F) : Set _)
  obtain ⟨a, ha, hau⟩ := boundary_attachment hm u hub
  obtain ⟨b, hb, hbv⟩ := boundary_attachment hm v hvb
  have hauH : H.Adj a (deepEmbedding hm u) :=
    ⟨hau, Or.inr ((mem_deepSelected hm F u).mp hu)⟩
  have hbvH : H.Adj b (deepEmbedding hm v) :=
    ⟨hbv, Or.inr ((mem_deepSelected hm F v).mp hv)⟩
  let K := H.deleteEdges {s(a, deepEmbedding hm u)}
  have : Subsingleton A.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hcA.le
  have hab : A.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := ConnectedComponent.exact (Subsingleton.elim _ _)
  have avoidA {x y : Vertex n} : s(x.1, y.1) ≠ s(a, deepEmbedding hm u) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, he⟩ | ⟨he, _⟩
    · exact deepEmbedding_not_mem hm u (he ▸ y.2)
    · exact deepEmbedding_not_mem hm u (he ▸ x.2)
  let incA : A →g K :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y h
        refine deleteEdges_adj.mpr ⟨⟨h.1, ?_⟩, ?_⟩
        · simpa only [selected, mem_filter, mem_univ, true_and, mem_coe] using h.2
        · simpa only [Set.mem_singleton_iff] using (avoidA (x := x) (y := y)) }
  let incD : forcedEdgeGraph (gridGraph m m) (↑(deepSelected hm F) : Set _) →g K :=
    { toFun := deepEmbedding hm
      map_rel' := by
        intro x y h
        refine deleteEdges_adj.mpr ⟨(deepHom hm F).map_rel h, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro he
        rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨_, he⟩
        · exact deepEmbedding_not_mem hm x (he ▸ ha)
        · exact deepEmbedding_not_mem hm y (he ▸ ha) }
  have hbvK : K.Adj b (deepEmbedding hm v) := by
    refine deleteEdges_adj.mpr ⟨hbvH, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, he⟩ | ⟨_, he⟩
    · exact hne ((deepEmbedding hm).injective he).symm
    · exact deepEmbedding_not_mem hm v (he ▸ ha)
  have hpath : K.Reachable a (deepEmbedding hm u) :=
    (hab.map incA).trans (hbvK.reachable.trans (hreach.symm.map incD))
  exact (isAcyclic_iff_forall_adj_isBridge.mp hacyc hauH) hpath

/-- A preserved deep corner has two distinct annulus contacts and would
close a physical cycle, independently of the other corner orientations. -/
theorem deep_corners_unpreserved {m n : Nat} (hm : m + 4 = n) (hmlo : 2 ≤ m)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcA : Fintype.card (forcedEdgeGraph (graph n)
      (↑(selected F) : Set _)).ConnectedComponent = 1) :
    ∀ v, Corner v → v ∉ deepSelected hm F := by
  intro v hv hvF
  let z := deepEmbedding hm v
  let r : Fin n := if v.1.val = 0 then ⟨1, by omega⟩ else ⟨n - 2, by omega⟩
  let c : Fin n := if v.2.val = 0 then ⟨1, by omega⟩ else ⟨n - 2, by omega⟩
  have hr : r.val = 1 ∨ r.val + 2 = n := by dsimp [r]; split_ifs <;> simp; omega
  have hc : c.val = 1 ∨ c.val + 2 = n := by dsimp [c]; split_ifs <;> simp; omega
  have hzr : z.1.val = 2 + v.1.val := rfl
  have hzc : z.2.val = 2 + v.2.val := rfl
  have har : r.val + 1 = z.1.val ∨ z.1.val + 1 = r.val := by
    dsimp [r]
    split_ifs <;> dsimp only <;> unfold Corner at hv <;> omega
  have hbc : z.2.val + 1 = c.val ∨ c.val + 1 = z.2.val := by
    dsimp [c]
    split_ifs <;> dsimp only <;> unfold Corner at hv <;> omega
  have hzF : z ∈ F := (mem_deepSelected hm F v).mp hvF
  apply outside_two_annulus_neighbors_false F hacyc hcA
    (a := (r, z.2)) (b := (z.1, c)) (z := z)
  · unfold Mem; dsimp; omega
  · unfold Mem; dsimp; omega
  · exact deepEmbedding_not_mem hm v
  · intro he
    have he' := congrArg (fun w : GridVertex n n => w.1.val) he
    change r.val = z.1.val at he'
    omega
  · refine ⟨?_, Or.inr hzF⟩
    simp only [gridGraph, adjacent, Fin.ext_iff]
    exact Or.inr ⟨True.intro, har⟩
  · refine ⟨?_, Or.inl hzF⟩
    simp only [gridGraph, adjacent, Fin.ext_iff]
    exact Or.inl ⟨True.intro, hbc⟩

end GridGraphs.BoundarySix.Connected
