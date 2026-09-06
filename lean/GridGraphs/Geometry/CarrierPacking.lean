import GridGraphs.Core.Forced

/-!
# Local packing of horizontal carriers

In an acyclic forced-edge graph, wholly forced intervals on rows two apart
overlap in at most one column. Their cardinalities therefore sum to at most
the grid width plus one. These are local bounds, not a global upper bound.
-/

namespace GridGraphs

open SimpleGraph

private lemma forced_six_cycle_false {V : Type*} (G : SimpleGraph V)
    {F : Set V} (hacyc : (forcedEdgeGraph G F).IsAcyclic)
    (v0 v1 v2 v3 v4 v5 : V)
    (hnodup : [v0, v1, v2, v3, v4, v5].Nodup)
    (h01 : G.Adj v0 v1) (h12 : G.Adj v1 v2)
    (h23 : G.Adj v2 v3) (h34 : G.Adj v3 v4)
    (h45 : G.Adj v4 v5) (h50 : G.Adj v5 v0)
    (hv0 : v0 ∈ F) (hv1 : v1 ∈ F) (hv3 : v3 ∈ F) (hv4 : v4 ∈ F) :
    False := by
  classical
  let H := forcedEdgeGraph G F
  have hg01 : H.Adj v0 v1 := ⟨h01, Or.inl hv0⟩
  have hg12 : H.Adj v1 v2 := ⟨h12, Or.inl hv1⟩
  have hg23 : H.Adj v2 v3 := ⟨h23, Or.inr hv3⟩
  have hg34 : H.Adj v3 v4 := ⟨h34, Or.inl hv3⟩
  have hg45 : H.Adj v4 v5 := ⟨h45, Or.inl hv4⟩
  have hg50 : H.Adj v5 v0 := ⟨h50, Or.inr hv0⟩
  let q : H.Walk v1 v0 := Walk.cons hg12 (Walk.cons hg23
    (Walk.cons hg34 (Walk.cons hg45 (Walk.cons hg50 Walk.nil))))
  let p : H.Walk v0 v0 := Walk.cons hg01 q
  have hqPath : q.IsPath := by
    simp_all [q, List.nodup_cons, eq_comm]
  have hg01Not : s(v0, v1) ∉ q.edges := by
    simp_all [q, List.nodup_cons, eq_comm]
  apply hacyc p
  change (Walk.cons hg01 q).IsCycle
  rw [Walk.cons_isCycle_iff]
  exact ⟨hqPath, hg01Not⟩

/-- The four corners of a two-row-step, one-column-step rectangle cannot
all be forced. The two middle-row vertices need no membership assumptions. -/
theorem forced_rectangle_two_rows_false {m n : Nat}
    (r : Fin (m - 2)) (c : Fin (n - 1))
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (h00 : (⟨r.val, by omega⟩, ⟨c.val, by omega⟩) ∈ F)
    (h01 : (⟨r.val, by omega⟩, ⟨c.val + 1, by omega⟩) ∈ F)
    (h20 : (⟨r.val + 2, by omega⟩, ⟨c.val, by omega⟩) ∈ F)
    (h21 : (⟨r.val + 2, by omega⟩, ⟨c.val + 1, by omega⟩) ∈ F) :
    False := by
  let r0 : Fin m := ⟨r.val, by omega⟩
  let r1 : Fin m := ⟨r.val + 1, by omega⟩
  let r2 : Fin m := ⟨r.val + 2, by omega⟩
  let c0 : Fin n := ⟨c.val, by omega⟩
  let c1 : Fin n := ⟨c.val + 1, by omega⟩
  apply forced_six_cycle_false (gridGraph m n) hacyc
    (r0, c0) (r0, c1) (r1, c1) (r2, c1) (r2, c0) (r1, c0)
    _ _ _ _ _ _ _ h00 h01 h21 h20
  · simp [List.nodup_cons, Prod.mk.injEq, Fin.ext_iff, r0, r1, r2, c0, c1]
  all_goals simp [gridGraph, adjacent, r0, r1, r2, c0, c1, Fin.ext_iff,
    Nat.add_assoc]

/-- Wholly forced horizontal intervals on rows two apart share at most one
column, including when either interval is empty. -/
theorem horizontal_carrier_intersection_card_le_one {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (r r2 : Fin m) (hrows : r.val + 2 = r2.val)
    (a b c d : Fin n)
    (hfirst : ∀ x ∈ Finset.Icc a b, (r, x) ∈ F)
    (hsecond : ∀ x ∈ Finset.Icc c d, (r2, x) ∈ F) :
    (Finset.Icc a b ∩ Finset.Icc c d).card ≤ 1 := by
  have no_pair (x y : Fin n)
      (hx : x ∈ Finset.Icc a b ∩ Finset.Icc c d)
      (hy : y ∈ Finset.Icc a b ∩ Finset.Icc c d)
      (hxy : x < y) : False := by
    have hx' := hx
    have hy' := hy
    simp only [Finset.mem_inter, Finset.mem_Icc, Fin.le_iff_val_le_val] at hx' hy'
    let next : Fin n := ⟨x.val + 1, by omega⟩
    have hnfirst : next ∈ Finset.Icc a b := by
      simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, next]
      constructor <;> omega
    have hnsecond : next ∈ Finset.Icc c d := by
      simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, next]
      constructor <;> omega
    let row : Fin (m - 2) := ⟨r.val, by omega⟩
    let col : Fin (n - 1) := ⟨x.val, by omega⟩
    have hr2 : (⟨row.val + 2, by omega⟩ : Fin m) = r2 := Fin.ext hrows
    apply forced_rectangle_two_rows_false row col hacyc
    · exact hfirst x (Finset.mem_inter.mp hx).1
    · exact hfirst next hnfirst
    · simpa only [hr2] using hsecond x (Finset.mem_inter.mp hx).2
    · simpa only [hr2] using hsecond next hnsecond
  apply Finset.card_le_one.mpr
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact (no_pair x y hx hy hxy).elim
  · exact hxy
  · exact (no_pair y x hy hx hyx).elim

/-- The lengths (interval cardinalities) of two wholly forced horizontal
intervals on rows two apart sum to at most `n + 1`. No nonemptiness is required. -/
theorem horizontal_carrier_card_sum_le {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (r r2 : Fin m) (hrows : r.val + 2 = r2.val)
    (a b c d : Fin n)
    (hfirst : ∀ x ∈ Finset.Icc a b, (r, x) ∈ F)
    (hsecond : ∀ x ∈ Finset.Icc c d, (r2, x) ∈ F) :
    (Finset.Icc a b).card + (Finset.Icc c d).card ≤ n + 1 := by
  have hinter := horizontal_carrier_intersection_card_le_one
    hacyc r r2 hrows a b c d hfirst hsecond
  have hunion : (Finset.Icc a b ∪ Finset.Icc c d).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hcard := Finset.card_union_add_card_inter (Finset.Icc a b) (Finset.Icc c d)
  omega

end GridGraphs
