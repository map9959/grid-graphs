import GridGraphs.GridCotreePorts

/-!
# Rooted fundamental shores of a grid tree

This file supplies the graph-theoretic prerequisites for using fundamental
tree shores globally.  A dart points away from a root when its target shore
does not contain the root.  Such shores form a laminar family, and membership
of an ambient edge in a fundamental cut is detected by the unique tree path
between its endpoints.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- A tree dart is oriented away from `root` when its target component after
deleting the underlying edge is the component not containing `root`. -/
def AwayFromRoot (root : GridVertex m n) (d : GridDirectionalDart T) : Prop :=
  root ∉ d.targetShoreVertices

private theorem reverse_edgeSym2 (d : GridDirectionalDart T) :
    d.reverse.edgeSym2 = d.edgeSym2 := by
  simp [edgeSym2, reverse, Sym2.eq_swap]

private theorem reachable_source_or_target (htree : T.IsTree)
    (d : GridDirectionalDart T) (v : GridVertex m n) :
    (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.source v ∨
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.target v := by
  obtain ⟨p⟩ := htree.isConnected.preconnected d.source v
  have walk_class : ∀ {u w : GridVertex m n} (q : T.Walk u w),
      ((T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.source u ∨
        (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.target u) →
      ((T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.source w ∨
        (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.target w) := by
    intro u w q hu
    induction q with
    | nil => exact hu
    | @cons u z w hadj q ih =>
        apply ih
        by_cases he : s(u, z) = d.edgeSym2
        · rw [edgeSym2, Sym2.eq_iff] at he
          rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · subst_vars
            exact Or.inr .rfl
          · subst_vars
            exact Or.inl .rfl
        · have hadj' :
              (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Adj u z := by
            rw [SimpleGraph.deleteEdges_adj]
            exact ⟨hadj, by simpa using he⟩
          rcases hu with hu | hu
          · exact Or.inl (hu.trans hadj'.reachable)
          · exact Or.inr (hu.trans hadj'.reachable)
  exact walk_class p (Or.inl .rfl)

/-- Every vertex of a tree lies on exactly the source side or the target side
of a deleted dart edge. -/
theorem mem_targetShoreVertices_or_reachable_source (htree : T.IsTree)
    (d : GridDirectionalDart T) (v : GridVertex m n) :
    v ∈ d.targetShoreVertices ∨
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.source v := by
  rcases reachable_source_or_target htree d v with h | h
  · exact Or.inr h
  · exact Or.inl ((mem_targetShoreVertices d v).2 h)

/-- A vertex is outside the target shore exactly when it is reachable from the
source after deleting the dart edge. -/
theorem not_mem_targetShoreVertices_iff_reachable_source (htree : T.IsTree)
    (d : GridDirectionalDart T) (v : GridVertex m n) :
    v ∉ d.targetShoreVertices ↔
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable d.source v := by
  constructor
  · intro hv
    exact (mem_targetShoreVertices_or_reachable_source htree d v).resolve_left hv
  · intro hv htarget
    have hst := ((mem_targetShoreVertices d v).1 htarget).trans hv.symm
    exact source_notMem_targetShoreVertices htree.IsAcyclic d
      ((mem_targetShoreVertices d d.source).2 hst)

/-- Reversing an edge exchanges its two fundamental shores. -/
theorem mem_reverse_targetShoreVertices_iff_not_mem (htree : T.IsTree)
    (d : GridDirectionalDart T) (v : GridVertex m n) :
    v ∈ d.reverse.targetShoreVertices ↔ v ∉ d.targetShoreVertices := by
  rw [mem_targetShoreVertices]
  rw [not_mem_targetShoreVertices_iff_reachable_source htree]
  rw [reverse_edgeSym2]
  rfl

/-- Exactly one orientation of a tree edge points away from a fixed root. -/
theorem awayFromRoot_reverse_iff_not (htree : T.IsTree)
    (root : GridVertex m n) (d : GridDirectionalDart T) :
    AwayFromRoot root d.reverse ↔ ¬AwayFromRoot root d := by
  simp only [AwayFromRoot]
  rw [mem_reverse_targetShoreVertices_iff_not_mem htree]

/-- The rooted orientation of an unordered tree edge exists and is unique
among its two directional darts. -/
theorem awayFromRoot_xor_reverse (htree : T.IsTree)
    (root : GridVertex m n) (d : GridDirectionalDart T) :
    Xor' (AwayFromRoot root d) (AwayFromRoot root d.reverse) := by
  rw [awayFromRoot_reverse_iff_not htree]
  simp

private theorem reachable_delete_of_reachable_of_target_not_reachable
    {a b u v : GridVertex m n}
    (ha : (T.deleteEdges ({s(a, b)} : Set (Sym2 (GridVertex m n)))).Reachable u v)
    {c e : GridVertex m n}
    (hc : ¬(T.deleteEdges ({s(a, b)} : Set (Sym2 (GridVertex m n)))).Reachable u c) :
    (T.deleteEdges ({s(c, e)} : Set (Sym2 (GridVertex m n)))).Reachable u v := by
  obtain ⟨p⟩ := ha
  let q := p.map (.ofLE (T.deleteEdges_le ({s(a, b)} : Set (Sym2 (GridVertex m n)))))
  have hce : s(c, e) ∉ q.edges := by
    intro hedge
    have hcSupport := q.fst_mem_support_of_mem_edges hedge
    let r := q.takeUntil c hcSupport
    have hab : s(a, b) ∉ r.edges := by
      intro hab
      have habq : s(a, b) ∈ q.edges := q.edges_takeUntil_subset hcSupport hab
      have hpab : s(a, b) ∈ p.edges := by simpa [q] using habq
      have hpedge := p.edges_subset_edgeSet hpab
      rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at hpedge
      exact hpedge.2 rfl
    exact hc ⟨r.toDeleteEdge s(a, b) hab⟩
  exact ⟨q.toDeleteEdge s(c, e) hce⟩

/-- Target shores of tree edges oriented away from one root are nested or
disjoint. -/
theorem targetShoreVertices_laminar (htree : T.IsTree)
    (root : GridVertex m n) {a b : GridDirectionalDart T}
    (ha : AwayFromRoot root a) (hb : AwayFromRoot root b) :
    a.targetShoreVertices ⊆ b.targetShoreVertices ∨
      b.targetShoreVertices ⊆ a.targetShoreVertices ∨
      Disjoint a.targetShoreVertices b.targetShoreVertices := by
  classical
  by_cases hi : ∃ x, x ∈ a.targetShoreVertices ∧ x ∈ b.targetShoreVertices
  · obtain ⟨x, hxa, hxb⟩ := hi
    by_cases hedge : a.edgeSym2 = b.edgeSym2
    · have hsides : a.targetShoreVertices = b.targetShoreVertices := by
        ext v
        by_cases hva : v ∈ a.targetShoreVertices
        · by_cases hvb : v ∈ b.targetShoreVertices
          · simp [hva, hvb]
          · have hra := (not_mem_targetShoreVertices_iff_reachable_source htree b v).1 hvb
            have hrootb := (not_mem_targetShoreVertices_iff_reachable_source htree b root).1 hb
            have hr := hrootb.symm.trans hra
            have hroota := (not_mem_targetShoreVertices_iff_reachable_source htree a root).1 ha
            have hs : (T.deleteEdges ({a.edgeSym2} : Set _)).Reachable root v := by
              simpa [hedge] using hr
            exact (ha ((mem_targetShoreVertices a root).2
              (((mem_targetShoreVertices a v).1 hva).trans hs.symm))).elim
        · by_cases hvb : v ∈ b.targetShoreVertices
          · have := (not_mem_targetShoreVertices_iff_reachable_source htree a v).1 hva
            have hroota := (not_mem_targetShoreVertices_iff_reachable_source htree a root).1 ha
            have hr := hroota.symm.trans this
            have hrootb := (not_mem_targetShoreVertices_iff_reachable_source htree b root).1 hb
            have hs : (T.deleteEdges ({b.edgeSym2} : Set _)).Reachable root v := by
              simpa [hedge] using hr
            exact (hb ((mem_targetShoreVertices b root).2
              (((mem_targetShoreVertices b v).1 hvb).trans hs.symm))).elim
          · simp [hva, hvb]
      exact Or.inl (by simpa [hsides])
    · by_cases hba : b.target ∈ a.targetShoreVertices
      · have hab : a.target ∉ b.targetShoreVertices := by
          intro hab
          have hbs : b.source ∈ a.targetShoreVertices := by
            rw [mem_targetShoreVertices]
            have hadj : (T.deleteEdges ({a.edgeSym2} : Set _)).Adj b.target b.source := by
              rw [SimpleGraph.deleteEdges_adj]
              exact ⟨b.adj.symm, by
                have hne : b.edgeSym2 ≠ a.edgeSym2 := Ne.symm hedge
                simpa [edgeSym2, Sym2.eq_swap] using hne⟩
            exact ((mem_targetShoreVertices a b.target).1 hba).trans hadj.reachable
          have hrb := (not_mem_targetShoreVertices_iff_reachable_source htree b root).1 hb
          have hra : ¬(T.deleteEdges ({b.edgeSym2} : Set _)).Reachable root a.target := by
            intro h
            exact hb ((mem_targetShoreVertices b root).2
              (((mem_targetShoreVertices b a.target).1 hab).trans h.symm))
          have htransfer := reachable_delete_of_reachable_of_target_not_reachable
            (T := T) (a := b.source) (b := b.target) (c := a.target) (e := a.source)
            (by simpa [edgeSym2] using hrb.symm) hra
          exact ha ((mem_targetShoreVertices a root).2
            (((mem_targetShoreVertices a b.source).1 hbs).trans
              (by simpa [edgeSym2, Sym2.eq_swap] using htransfer.symm)))
        right; left
        intro v hv
        rw [mem_targetShoreVertices] at hv ⊢
        have hbToV : (T.deleteEdges ({a.edgeSym2} : Set _)).Reachable b.target v := by
          simpa [edgeSym2, Sym2.eq_swap] using
            (reachable_delete_of_reachable_of_target_not_reachable
            (T := T) (a := b.source) (b := b.target) (c := a.target) (e := a.source)
            (by simpa [edgeSym2] using hv)
            (by simpa only [mem_targetShoreVertices] using hab))
        exact ((mem_targetShoreVertices a b.target).1 hba).trans hbToV
      · left
        intro v hv
        rw [mem_targetShoreVertices] at hv ⊢
        have hax := (mem_targetShoreVertices a x).1 hxa
        have hbx := (mem_targetShoreVertices b x).1 hxb
        have haToX : (T.deleteEdges ({b.edgeSym2} : Set _)).Reachable a.target x := by
          simpa [edgeSym2, Sym2.eq_swap] using
            (reachable_delete_of_reachable_of_target_not_reachable
            (T := T) (a := a.source) (b := a.target) (c := b.target) (e := b.source)
            hax (by simpa only [mem_targetShoreVertices] using hba))
        have haToV : (T.deleteEdges ({b.edgeSym2} : Set _)).Reachable a.target v := by
          simpa [edgeSym2, Sym2.eq_swap] using
            (reachable_delete_of_reachable_of_target_not_reachable
              (T := T) (a := a.source) (b := a.target) (c := b.target) (e := b.source)
              hv (by simpa only [mem_targetShoreVertices] using hba))
        exact hbx.trans (haToX.symm.trans haToV)
  · right; right
    rw [Finset.disjoint_left]
    intro x hxa hxb
    exact hi ⟨x, hxa, hxb⟩

/-- For a path in a tree, a dart's attachment edge occurs on the path exactly
when the path endpoints lie on opposite sides of its fundamental cut. -/
theorem crosses_targetShoreVertices_iff_mem_path_edges (htree : T.IsTree)
    (d : GridDirectionalDart T) {u v : GridVertex m n}
    (p : T.Walk u v) (hp : p.IsPath) :
    ((u ∈ d.targetShoreVertices ∧ v ∉ d.targetShoreVertices) ∨
      (v ∈ d.targetShoreVertices ∧ u ∉ d.targetShoreVertices)) ↔
      d.edgeSym2 ∈ p.edges := by
  constructor
  · intro hcross
    by_contra hedge
    have huv : (T.deleteEdges ({d.edgeSym2} : Set _)).Reachable u v :=
      ⟨p.toDeleteEdge d.edgeSym2 hedge⟩
    rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact hv ((mem_targetShoreVertices d v).2
        (((mem_targetShoreVertices d u).1 hu).trans huv))
    · exact hu ((mem_targetShoreVertices d u).2
        (((mem_targetShoreVertices d v).1 hv).trans huv.symm))
  · intro hedge
    by_cases hu : u ∈ d.targetShoreVertices
    · by_cases hv : v ∈ d.targetShoreVertices
      · exfalso
        have huv := ((mem_targetShoreVertices d u).1 hu).symm.trans
          ((mem_targetShoreVertices d v).1 hv)
        obtain ⟨q⟩ := huv
        let qT := q.map (.ofLE (T.deleteEdges_le ({d.edgeSym2} : Set _)))
        change T.Walk u v at qT
        have heq := htree.IsAcyclic.path_unique (⟨p, hp⟩ : T.Path u v) qT.toPath
        have hpq : p = (qT.toPath : T.Walk u v) := congrArg Subtype.val heq
        rw [hpq] at hedge
        have hq := qT.edges_toPath_subset hedge
        have hnot : d.edgeSym2 ∉ qT.edges := by
          intro h
          have hq : d.edgeSym2 ∈ q.edges := by simpa [qT] using h
          have hqe := q.edges_subset_edgeSet hq
          rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at hqe
          exact hqe.2 rfl
        exact hnot hq
      · exact Or.inl ⟨hu, hv⟩
    · by_cases hv : v ∈ d.targetShoreVertices
      · exact Or.inr ⟨hv, hu⟩
      · exfalso
        have huv := (not_mem_targetShoreVertices_iff_reachable_source htree d u).1 hu |>.symm.trans
          ((not_mem_targetShoreVertices_iff_reachable_source htree d v).1 hv)
        obtain ⟨q⟩ := huv
        let qT := q.map (.ofLE (T.deleteEdges_le ({d.edgeSym2} : Set _)))
        change T.Walk u v at qT
        have heq := htree.IsAcyclic.path_unique (⟨p, hp⟩ : T.Path u v) qT.toPath
        have hpq : p = (qT.toPath : T.Walk u v) := congrArg Subtype.val heq
        rw [hpq] at hedge
        have hq := qT.edges_toPath_subset hedge
        have hnot : d.edgeSym2 ∉ qT.edges := by
          intro h
          have hq : d.edgeSym2 ∈ q.edges := by simpa [qT] using h
          have hqe := q.edges_subset_edgeSet hq
          rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at hqe
          exact hqe.2 rfl
        exact hnot hq

/-- A coordinate edge crosses a fundamental tree shore exactly when the
attachment edge lies on the unique tree path between its endpoints. -/
theorem gridEdge_crosses_targetShore_iff_mem_path_edges (htree : T.IsTree)
    (d : GridDirectionalDart T) (e : GridEdge m n)
    (p : T.Walk e.primalEndpoints.1 e.primalEndpoints.2) (hp : p.IsPath) :
    e.Crosses d.targetShoreVertices ↔ d.edgeSym2 ∈ p.edges :=
  crosses_targetShoreVertices_iff_mem_path_edges htree d p hp

/-- A cotree port crosses precisely those rooted fundamental tree edges that
occur on the unique tree path between the port's endpoints. -/
theorem mem_cotreePorts_iff_mem_path_edges (htree : T.IsTree)
    (d : GridDirectionalDart T) (e : GridEdge m n)
    (he : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2)
    (p : T.Walk e.primalEndpoints.1 e.primalEndpoints.2) (hp : p.IsPath) :
    e ∈ d.cotreePorts ↔ d.edgeSym2 ∈ p.edges := by
  rw [mem_cotreePorts, and_iff_left he]
  exact gridEdge_crosses_targetShore_iff_mem_path_edges htree d e p hp

end GridDirectionalDart

end GridGraphs
