import Mathlib

/-!
# Forest extension lemma

A standalone, generic lemma:

> Any acyclic subgraph of a finite connected graph extends to a spanning
> tree of the connected graph.

This generalises mathlib's `SimpleGraph.Connected.exists_isTree_le` (which
is the case `F = ⊥`). Used in `GridGraphs/DoubleComb.lean` and elsewhere
when the diagonal residue-1 lower bound is converted from a forced-edge
forest to an actual spanning tree.

The proof follows mathlib's pattern for `isTree_of_minimal_connected`:
take a minimal connected supergraph of `F` inside `G`, then show every
non-`F` edge is a bridge (else minimality is violated) and every cycle
must therefore live entirely in `F` (contradicting `F.IsAcyclic`).
-/

namespace SimpleGraph

/-- Forest extension: any acyclic subgraph of a finite connected graph
extends to a spanning tree. -/
theorem isAcyclic_extends_to_isTree {V : Type*} [Fintype V] [DecidableEq V]
    {G F : SimpleGraph V} [DecidableRel G.Adj]
    (hF_le : F ≤ G) (hF_acyc : F.IsAcyclic) (hG_conn : G.Connected) :
    ∃ T : SimpleGraph V, F ≤ T ∧ T ≤ G ∧ T.IsTree := by
  -- The candidate set: connected supergraphs of F inside G.
  let S : Set (SimpleGraph V) :=
    {H | F ≤ H ∧ H ≤ G ∧ H.Connected}
  -- S is non-empty: take any spanning tree T₀ of G, then T₀ ⊔ F ∈ S.
  obtain ⟨T₀, hT₀_le, hT₀_tree⟩ := hG_conn.exists_isTree_le
  have hT₀_conn : T₀.Connected := hT₀_tree.isConnected
  have hUnion_in_S : (T₀ ⊔ F) ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · -- F ≤ T₀ ⊔ F
      exact le_sup_right
    · -- T₀ ⊔ F ≤ G
      exact sup_le hT₀_le hF_le
    · -- (T₀ ⊔ F).Connected via Connected.mono
      exact hT₀_conn.mono le_sup_left
  -- S is finite (subset of the finite type SimpleGraph V).
  have hS_finite : S.Finite := Set.toFinite S
  -- Pick a minimal element of S that is ≤ T₀ ⊔ F.
  obtain ⟨T, hT_le_T₀F, hT_min⟩ := hS_finite.exists_le_minimal hUnion_in_S
  obtain ⟨hF_le_T, hT_le_G, hT_conn⟩ := hT_min.prop
  -- Prove T.IsAcyclic.
  have hT_acyc : T.IsAcyclic := by
    intro v c hc
    -- c : T.Walk v v with c.IsCycle. Show every edge of c is in F.
    have hCedge_in_F : ∀ e ∈ c.edges, e ∈ F.edgeSet := by
      intro e he
      by_contra hnotF
      -- e ∉ F.edgeSet ⇒ removing e from T keeps F ⊆ result and yields
      -- a graph still in S, strictly smaller than T. Contradicts minimality.
      -- Get u, w with e = s(u, w).
      obtain ⟨u, w, rfl⟩ : ∃ u w : V, e = s(u, w) := by
        induction e using Sym2.ind with
        | _ u w => exact ⟨u, w, rfl⟩
      have hadj_T : T.Adj u w := by
        have := c.adj_of_mem_edges he
        exact this
      -- e is non-bridge of T: it lies on cycle c.
      have hnonBridge : ¬ T.IsBridge s(u, w) := by
        rw [isBridge_iff_adj_and_forall_cycle_notMem]
        push_neg
        intro _
        exact ⟨v, c, hc, he⟩
      -- T.deleteEdges {s(u, w)} is connected.
      have hDel_conn : (T.deleteEdges {s(u, w)}).Connected :=
        hT_conn.connected_delete_edge_of_not_isBridge hnonBridge
      -- F ≤ T.deleteEdges {s(u, w)}.
      have hF_le_del : F ≤ T.deleteEdges {s(u, w)} := by
        intro x y hxy
        rw [deleteEdges_adj]
        refine ⟨hF_le_T hxy, ?_⟩
        intro hin
        rw [Set.mem_singleton_iff] at hin
        -- hin : s(x, y) = s(u, w). So s(u, w) ∈ F.edgeSet (since F.Adj x y).
        apply hnotF
        rw [← hin]
        rw [SimpleGraph.mem_edgeSet]
        exact hxy
      -- T.deleteEdges {s(u, w)} ≤ G.
      have hDel_le_G : T.deleteEdges {s(u, w)} ≤ G := by
        intro x y hxy
        exact hT_le_G (T.deleteEdges_le _ hxy)
      -- T.deleteEdges {s(u, w)} ∈ S.
      have hDel_in_S : T.deleteEdges {s(u, w)} ∈ S :=
        ⟨hF_le_del, hDel_le_G, hDel_conn⟩
      -- T.deleteEdges {s(u, w)} < T (strictly).
      have hStrict : T.deleteEdges {s(u, w)} < T := by
        rw [← edgeSet_ssubset_edgeSet]
        constructor
        · intro x hx
          rw [edgeSet_deleteEdges] at hx
          exact hx.1
        · intro hsub
          have h1 : s(u, w) ∈ T.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact hadj_T
          have h2 : s(u, w) ∉ (T.deleteEdges {s(u, w)}).edgeSet := by
            rw [edgeSet_deleteEdges]
            simp
          exact h2 (hsub h1)
      -- This contradicts T_min: T is minimal in S, but T.deleteEdges < T also in S.
      exact absurd hDel_in_S (hT_min.not_prop_of_lt hStrict)
    -- Now all edges of c are in F. Transfer the cycle to F.
    have hF_edge : ∀ e ∈ c.edges, e ∈ F.edgeSet := hCedge_in_F
    have hc_F : (c.transfer F hF_edge).IsCycle := hc.transfer hF_edge
    -- F.IsAcyclic forbids any cycle.
    exact hF_acyc (c.transfer F hF_edge) hc_F
  -- Conclude T.IsTree.
  refine ⟨T, hF_le_T, hT_le_G, ?_, hT_acyc⟩
  exact hT_conn

end SimpleGraph
