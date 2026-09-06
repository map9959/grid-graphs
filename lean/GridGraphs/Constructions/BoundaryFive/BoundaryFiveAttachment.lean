import GridGraphs.Constructions.BoundaryFive.BoundaryFiveFrame

/-! # Attachment to the canonical boundary-five frame

The once-cropped square uses zero-based coordinates `1 .. n - 2`.
Inner components may be unattached, and all isolated vertices are retained.
-/

namespace GridGraphs.BoundaryFiveAttachment

open SimpleGraph BoundaryFiveFrame

/-- The once-cropped square, on the original vertex type. -/
def I (n : Nat) : Set (GridVertex n n) :=
  {v | 1 ≤ v.1.val ∧ v.1.val ≤ n - 2 ∧
    1 ≤ v.2.val ∧ v.2.val ≤ n - 2}

theorem not_boundary_of_mem_I {n : Nat} {v : GridVertex n n}
    (hv : v ∈ I n) : ¬ IsGridBoundary v := by
  change 1 ≤ v.1.val ∧ v.1.val ≤ n - 2 ∧
    1 ≤ v.2.val ∧ v.2.val ≤ n - 2 at hv
  unfold IsGridBoundary
  omega

/-- No outer-frame edge has both endpoints in the crop. -/
theorem not_adj_of_mem_I {n : Nat} {x y : GridVertex n n}
    (hx : x ∈ I n) (hy : y ∈ I n) : ¬ (Houter n).Adj x y := by
  rintro ⟨_, hxF | hyF⟩
  · exact not_boundary_of_mem_I hx hxF.1
  · exact not_boundary_of_mem_I hy hyF.1

/-- Stop at the first frame vertex reached along inner edges. -/
private theorem crossing {V : Type*} {G J : SimpleGraph V} {u v : V}
    (p : (G ⊔ J).Walk u v) (hu : u ∈ J.support) (hv : v ∈ G.support) :
    ∃ y ∈ p.support, y ∈ G.support ∩ J.support ∧ J.Reachable u y := by
  induction p with
  | nil => exact ⟨_, by simp, ⟨hv, hu⟩, .refl _⟩
  | @cons u v w h p ih =>
      rcases h with hg | hj
      · exact ⟨u, by simp,
          ⟨⟨v, hg⟩, hu⟩, .refl _⟩
      · obtain ⟨y, hy, hyS, hr⟩ := ih ⟨u, hj.symm⟩ hv
        exact ⟨y, by simp [hy], hyS, hj.reachable.trans hr⟩

/-- A simple path between frame vertices cannot make an inner excursion. -/
private theorem path_edges_left {V : Type*} {G J : SimpleGraph V}
    (hattach : ∀ x ∈ G.support ∩ J.support, ∀ y ∈ G.support ∩ J.support,
      J.Reachable x y → x = y)
    {u v : V} (p : (G ⊔ J).Walk u v) (hp : p.IsPath)
    (hu : u ∈ G.support) (hv : v ∈ G.support) :
    ∀ e ∈ p.edges, e ∈ G.edgeSet := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      have hp' := (Walk.cons_isPath_iff h p).mp hp
      rcases h with hg | hj
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hg
        · exact ih hp'.1 ⟨u, hg.symm⟩ hv e he
      · obtain ⟨y, hy, hyS, hr⟩ := crossing p ⟨u, hj.symm⟩ hv
        have heq := hattach u ⟨hu, ⟨v, hj⟩⟩ y hyS (hj.reachable.trans hr)
        exact False.elim (hp'.2 (heq ▸ hy))

private theorem acyclic_sup {V : Type*} {G J : SimpleGraph V}
    (hG : G.IsAcyclic) (hJ : J.IsAcyclic)
    (hattach : ∀ x ∈ G.support ∩ J.support, ∀ y ∈ G.support ∩ J.support,
      J.Reachable x y → x = y) : (G ⊔ J).IsAcyclic := by
  classical
  -- Frame edges remain bridges; a cycle would therefore lie entirely in J.
  have bridge {u v : V} (h : G.Adj u v) : (G ⊔ J).IsBridge s(u, v) := by
    rw [isBridge_iff_forall_walk_mem_edges]
    intro p
    let q := p.toPath
    have he := path_edges_left hattach q.val q.property ⟨v, h⟩ ⟨u, h.symm⟩
    have hb := (isAcyclic_iff_forall_adj_isBridge.mp hG h)
    have hm := (isBridge_iff_forall_walk_mem_edges.mp hb) (q.val.transfer G he)
    have hm' : s(u, v) ∈ q.val.edges := by simpa using hm
    exact p.edges_toPath_subset_edges hm'
  intro u c hc
  have he : ∀ e ∈ c.edges, e ∈ J.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
        rcases c.edges_subset_edgeSet he with hg | hj
        · exact False.elim ((bridge hg).notMem_edges_of_isCycle hc he)
        · exact hj
  exact hJ (c.transfer J he) (hc.transfer he)

/-- Sufficiency allows arbitrary inner edges and unattached components. -/
theorem Houter_sup_isAcyclic {n : Nat} (hn : 7 ≤ n)
    (J : SimpleGraph (GridVertex n n))
    (hinside : ∀ ⦃x y⦄, J.Adj x y → x ∈ I n ∧ y ∈ I n)
    (hJ : J.IsAcyclic)
    (hattach : ∀ x ∈ (Houter n).support ∩ I n,
      ∀ y ∈ (Houter n).support ∩ I n, J.Reachable x y → x = y) :
    (Houter n ⊔ J).IsAcyclic := by
  apply acyclic_sup (Houter_isAcyclic hn) hJ
  intro x hx y hy hr
  obtain ⟨x', hx'⟩ := hx.2
  obtain ⟨y', hy'⟩ := hy.2
  exact hattach x ⟨hx.1, (hinside hx').1⟩ y ⟨hy.1, (hinside hy').1⟩ hr

/-- Exact attachment criterion for the canonical frame and the once-cropped square. -/
theorem Houter_sup_isAcyclic_iff {n : Nat} (hn : 7 ≤ n)
    (J : SimpleGraph (GridVertex n n))
    (hinside : ∀ ⦃x y⦄, J.Adj x y → x ∈ I n ∧ y ∈ I n) :
    (Houter n ⊔ J).IsAcyclic ↔ J.IsAcyclic ∧
      ∀ x ∈ (Houter n).support ∩ I n,
        ∀ y ∈ (Houter n).support ∩ I n, J.Reachable x y → x = y := by
  classical
  constructor
  · intro h
    refine ⟨h.anti le_sup_right, ?_⟩
    intro x hx y hy hr
    have hrG : (Houter n).Reachable x y :=
      ((support_isTree hn).connected.preconnected ⟨x, hx.1⟩ ⟨y, hy.1⟩).map
        (Embedding.induce _).toHom
    obtain ⟨p, hp⟩ := hrG.exists_isPath
    obtain ⟨q, hq⟩ := hr.exists_isPath
    have heq := (h.subsingleton_path x y).elim
      ⟨p.mapLe le_sup_left, (Walk.isPath_mapLe le_sup_left).mpr hp⟩
      ⟨q.mapLe le_sup_right, (Walk.isPath_mapLe le_sup_right).mpr hq⟩
    have hedges : p.edges = q.edges := by
      simpa using congrArg (fun r : (Houter n ⊔ J).Path x y => r.val.edges) heq
    cases p with
    | nil => rfl
    | @cons x z y hxz p =>
        have hm : s(x, z) ∈ q.edges := by rw [← hedges]; simp
        have hj : J.Adj x z := q.edges_subset_edgeSet hm
        exact False.elim (not_adj_of_mem_I (hinside hj).1 (hinside hj).2 hxz)
  · rintro ⟨hJ, ha⟩
    exact Houter_sup_isAcyclic hn J hinside hJ ha

end GridGraphs.BoundaryFiveAttachment
