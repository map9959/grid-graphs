import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Cuts in rooted forests

Root paths in a forest determine useful separators even when the forest is not
connected.  The statements here use explicit paths to a common root, so no
global connectedness or finiteness assumption is needed.
-/

namespace SimpleGraph

variable {V : Type*} {H K : SimpleGraph V}

/-- The first edge of a nontrivial path to a root occurs either on any walk to
another rooted vertex or on that vertex's path to the root. -/
theorem IsAcyclic.firstEdge_mem_connecting_or_otherRoot (hH : H.IsAcyclic)
    {x y r : V} (px : H.Walk x r) (hpx : px.IsPath)
    (py : H.Walk y r) (q : H.Walk x y) (hnil : ¬px.Nil) :
    s(x, px.snd) ∈ q.edges ∨ s(x, px.snd) ∈ py.edges := by
  have hbridge : H.IsBridge s(x, px.snd) :=
    (isAcyclic_iff_forall_adj_isBridge.mp hH) (px.adj_snd hnil)
  have hedge := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge).2
    ((q.append py).append px.tail.reverse)
  simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append,
    List.mem_reverse] at hedge
  rcases hedge with (hq | hpy) | htail
  · exact Or.inl hq
  · exact Or.inr hpy
  · have hcons : (Walk.cons (px.adj_snd hnil) px.tail).IsPath := by
      rw [px.cons_tail_eq hnil]
      exact hpx
    have hxnot : x ∉ px.tail.support :=
      (Walk.cons_isPath_iff (px.adj_snd hnil) px.tail).mp hcons |>.2
    exact (hxnot (px.tail.fst_mem_support_of_mem_edges htail)).elim

/-- Removing the first root edge at each of two distinct rooted vertices
separates them in every subgraph of the forest.  If an endpoint is the root,
its root path is nil and only the other endpoint's condition is used. -/
theorem IsAcyclic.not_reachable_of_firstEdge_not_adj
    (hH : H.IsAcyclic) (hKH : K ≤ H) {x y r : V}
    (px : H.Walk x r) (hpx : px.IsPath)
    (py : H.Walk y r) (hpy : py.IsPath) (hxy : x ≠ y)
    (hxcut : ¬px.Nil → ¬K.Adj x px.snd)
    (hycut : ¬py.Nil → ¬K.Adj y py.snd) :
    ¬K.Reachable x y := by
  classical
  rintro ⟨q⟩
  let qH : H.Walk x y := q.mapLe hKH
  have qH_edges : qH.edges = q.edges := by
    simp [qH]
  by_cases hpxnil : px.Nil
  · have hxr : x = r := hpxnil.eq
    have hyr : y ≠ r := by
      intro hyr
      exact hxy (hxr.trans hyr.symm)
    have hpynil : ¬py.Nil := Walk.not_nil_of_ne hyr
    rcases hH.firstEdge_mem_connecting_or_otherRoot py hpy px qH.reverse hpynil with
      hq | hpxedge
    · apply hycut hpynil
      apply q.adj_of_mem_edges
      rw [Walk.edges_reverse, List.mem_reverse, qH_edges] at hq
      exact hq
    · subst x
      rw [Walk.Nil.eq_nil hpxnil] at hpxedge
      simp at hpxedge
  · by_cases hpynil : py.Nil
    · rcases hH.firstEdge_mem_connecting_or_otherRoot px hpx py qH hpxnil with
        hq | hpyedge
      · apply hxcut hpxnil
        apply q.adj_of_mem_edges
        rw [qH_edges] at hq
        exact hq
      · have hyr : y = r := hpynil.eq
        subst y
        rw [Walk.Nil.eq_nil hpynil] at hpyedge
        simp at hpyedge
    · have hxother : s(x, px.snd) ∈ py.edges := by
        rcases hH.firstEdge_mem_connecting_or_otherRoot px hpx py qH hpxnil with
          hq | hpyedge
        · exact (hxcut hpxnil (q.adj_of_mem_edges (qH_edges ▸ hq))).elim
        · exact hpyedge
      have hyother : s(y, py.snd) ∈ px.edges := by
        rcases hH.firstEdge_mem_connecting_or_otherRoot py hpy px qH.reverse hpynil with
          hq | hpxedge
        · have hq' : s(y, py.snd) ∈ q.edges := by
            rw [Walk.edges_reverse, List.mem_reverse, qH_edges] at hq
            exact hq
          exact (hycut hpynil (q.adj_of_mem_edges hq')).elim
        · exact hpxedge
      have hxmem : x ∈ py.support := py.fst_mem_support_of_mem_edges hxother
      have hymem : y ∈ px.support := px.fst_mem_support_of_mem_edges hyother
      have heq : px = py.dropUntil x hxmem := by
        exact congrArg Subtype.val
          (hH.path_unique ⟨px, hpx⟩ ⟨py.dropUntil x hxmem, hpy.dropUntil hxmem⟩)
      have hymem' : y ∈ (py.dropUntil x hxmem).support := by
        rwa [← heq]
      have hsplit : ((py.takeUntil x hxmem).append
          (py.dropUntil x hxmem)).IsPath := by
        rw [py.take_spec hxmem]
        exact hpy
      have hne : y ≠ y := hsplit.ne_of_mem_support_of_append hxy.symm
        (py.takeUntil x hxmem).start_mem_support hymem'
      exact hne rfl

end SimpleGraph
