import GridGraphs.Accounting.CarrierLayers.RadialSideGeometry

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

private lemma six_cycle_false {V : Type*} (G : SimpleGraph V)
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

private def axisVertex {n : Nat} (horizontal : Bool) (r c : Fin n) : GridVertex n n :=
  if horizontal then (r, c) else (c, r)

private theorem rectangle_gap_two_false {n : Nat} (horizontal : Bool)
    (r t i j : Fin n) (hrt : r.val + 1 = t.val ∨ t.val + 1 = r.val)
    (hij : i.val + 2 = j.val) {F : Set (GridVertex n n)}
    (hacyc : (forcedEdgeGraph (gridGraph n n) F).IsAcyclic)
    (hu : axisVertex horizontal r i ∈ F) (hw : axisVertex horizontal t i ∈ F)
    (hv : axisVertex horizontal r j ∈ F) (hz : axisVertex horizontal t j ∈ F) :
    False := by
  let mid : Fin n := ⟨i.val + 1, by omega⟩
  apply six_cycle_false (gridGraph n n) hacyc
    (axisVertex horizontal r i) (axisVertex horizontal t i)
    (axisVertex horizontal t mid) (axisVertex horizontal t j)
    (axisVertex horizontal r j) (axisVertex horizontal r mid)
    _ _ _ _ _ _ _ hu hw hz hv
  · cases horizontal <;>
      simp [axisVertex, List.nodup_cons, Prod.mk.injEq, Fin.ext_iff, mid] <;> omega
  all_goals cases horizontal <;>
    simp [axisVertex, gridGraph, adjacent, Fin.ext_iff, mid] <;> omega

/-- The coordinate running along an outer side. -/
def sidePosition {n : Nat} (s : Fin 4) (v : GridVertex n n) : Nat :=
  if s.val < 2 then v.2.val else v.1.val

/-- Preserved radial pairs on an open side are separated by at least three
positions: a gap of one makes a unit cycle, a gap of two makes a six-cycle. -/
theorem radial_pair_spacing {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) {u v w z : GridVertex n n}
    (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F) (hz : z ∈ F)
    (hus : OnOpenSide s u) (hvs : OnOpenSide s v)
    (hwr : IsNextRing w) (hzr : IsNextRing z)
    (huw : (gridGraph n n).Adj u w) (hvz : (gridGraph n n).Adj v z)
    (hlt : sidePosition s u < sidePosition s v) :
    sidePosition s u + 3 ≤ sidePosition s v := by
  have hadjuw := huw
  have hadjvz := hvz
  simp only [gridGraph, adjacent, Fin.ext_iff] at hadjuw hadjvz
  have hus' := hus
  have hvs' := hvs
  unfold OnOpenSide OnSide at hus' hvs'
  unfold IsNextRing at hwr hzr
  by_contra hgap
  by_cases haxis : s.val < 2
  · have hrow : u.1 = v.1 := Fin.ext (by omega)
    have hwcol : w.2 = u.2 := Fin.ext (by omega)
    have hzcol : z.2 = v.2 := Fin.ext (by omega)
    have hwrow : w.1 = z.1 := Fin.ext (by omega)
    have hstep : u.1.val + 1 = w.1.val ∨ w.1.val + 1 = u.1.val := by omega
    simp only [sidePosition, if_pos haxis] at hlt hgap
    have hcases : u.2.val + 1 = v.2.val ∨ u.2.val + 2 = v.2.val := by omega
    rcases hcases with h1 | h2
    · have hadj : (gridGraph n n).Adj u v := Or.inl ⟨hrow, Or.inl h1⟩
      have hp := forced_two_edge_walk_parallel hacyc hw hu hv huw.symm hadj
      simp only [Fin.ext_iff] at hp
      omega
    · apply rectangle_gap_two_false true u.1 w.1 u.2 v.2 hstep h2 hacyc
      · exact hu
      · simpa [axisVertex, ← hwcol] using hw
      · simpa [axisVertex, hrow] using hv
      · simpa [axisVertex, hwrow, ← hzcol] using hz
  · have hcol : u.2 = v.2 := Fin.ext (by omega)
    have hwrow : w.1 = u.1 := Fin.ext (by omega)
    have hzrow : z.1 = v.1 := Fin.ext (by omega)
    have hwcol : w.2 = z.2 := Fin.ext (by omega)
    have hstep : u.2.val + 1 = w.2.val ∨ w.2.val + 1 = u.2.val := by omega
    simp only [sidePosition, if_neg haxis] at hlt hgap
    have hcases : u.1.val + 1 = v.1.val ∨ u.1.val + 2 = v.1.val := by omega
    rcases hcases with h1 | h2
    · have hadj : (gridGraph n n).Adj u v := Or.inr ⟨hcol, Or.inl h1⟩
      have hp := forced_two_edge_walk_parallel hacyc hw hu hv huw.symm hadj
      simp only [Fin.ext_iff] at hp
      omega
    · apply rectangle_gap_two_false false u.2 w.2 u.1 v.1 hstep h2 hacyc
      · exact hu
      · simpa [axisVertex, ← hwrow] using hw
      · simpa [axisVertex, hcol] using hv
      · simpa [axisVertex, hwcol, ← hzrow] using hz

end GridGraphs.CarrierLayers
