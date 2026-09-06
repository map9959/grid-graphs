import GridGraphs.Core.Forced
import GridGraphs.Core.ForcedMaximum

/-!
# One-vertex exchange for forced forests
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

private def addEdge (H : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj x y := H.Adj x y ∨
    (((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ x ≠ y)
  symm := by
    constructor
    rintro x y (h | ⟨h, hxy⟩)
    · exact Or.inl (Adj.symm h)
    · exact Or.inr ⟨h.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩), hxy.symm⟩
  loopless := ⟨by intro x; simp⟩

private lemma addEdge_adj {H : SimpleGraph V} {u v x y : V} :
    (addEdge H u v).Adj x y ↔ H.Adj x y ∨
      (((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ x ≠ y) := Iff.rfl

private lemma delete_added_edge {H : SimpleGraph V} {u v : V}
    (huv : u ≠ v) (hnew : ¬H.Adj u v) :
    addEdge H u v \ fromEdgeSet {s(u, v)} = H := by
  ext x y
  simp only [sdiff_adj, addEdge_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hH | ⟨_, _⟩, hnot⟩
    · exact hH
    · exfalso
      apply hnot
      rcases ‹(x = u ∧ y = v) ∨ (x = v ∧ y = u)› with h | h
      · exact ⟨Or.inl h, h.1 ▸ h.2 ▸ huv⟩
      · exact ⟨Or.inr h, h.1 ▸ h.2 ▸ huv.symm⟩
  · intro hH
    refine ⟨Or.inl hH, ?_⟩
    rintro ⟨h | h, _⟩
    · exact hnew (h.1 ▸ h.2 ▸ hH)
    · exact hnew (Adj.symm (h.1 ▸ h.2 ▸ hH))

/-- Adding a genuinely new edge to a forest is acyclic exactly when its
endpoints were in different components. -/
private theorem isAcyclic_addEdge_iff {H : SimpleGraph V} {u v : V}
    (hH : H.IsAcyclic) (huv : u ≠ v) (hnew : ¬H.Adj u v) :
    (addEdge H u v).IsAcyclic ↔ ¬H.Reachable u v := by
  let K := addEdge H u v
  have hdel : K \ fromEdgeSet {s(u, v)} = H :=
    delete_added_edge huv hnew
  constructor
  · intro hK huvReach
    obtain ⟨x, c, hc, _⟩ :=
      (adj_and_reachable_delete_edges_iff_exists_cycle
        (G := K) (v := u) (w := v)).mp ⟨by
          exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩, by simpa [deleteEdges, hdel]⟩
    exact hK c hc
  · intro hnreach x c hc
    by_cases he : s(u, v) ∈ c.edges
    · have hreach := (adj_and_reachable_delete_edges_iff_exists_cycle
        (G := K) (v := u) (w := v)).mpr ⟨x, c, hc, he⟩ |>.2
      exact hnreach (by simpa [deleteEdges, hdel] using hreach)
    · have hedges : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
        intro e hec
        have heK := c.edges_subset_edgeSet hec
        induction e using Sym2.ind with
        | _ a b =>
          change K.Adj a b at heK
          rcases heK with heH | ⟨hab, _⟩
          · exact heH
          · apply (he ?_).elim
            rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hec
            · simpa [Sym2.eq_swap] using hec
      exact hH (c.transfer H hedges) (hc.transfer hedges)

private def fanGraph (H : SimpleGraph V) (u : V) (S : Finset V) : SimpleGraph V where
  Adj x y := H.Adj x y ∨
    ((((x = u ∧ y ∈ S) ∨ (y = u ∧ x ∈ S))) ∧ x ≠ y)
  symm := by
    constructor
    rintro x y (h | ⟨h, hxy⟩)
    · exact Or.inl (Adj.symm h)
    · exact Or.inr ⟨h.elim (fun h => Or.inr ⟨h.1, h.2⟩)
        (fun h => Or.inl ⟨h.1, h.2⟩), hxy.symm⟩
  loopless := ⟨by intro x; simp⟩

private lemma fanGraph_insert [DecidableEq V] (H : SimpleGraph V) (u v : V)
    (S : Finset V) :
    fanGraph H u (insert v S) = addEdge (fanGraph H u S) u v := by
  ext x y
  simp only [fanGraph, addEdge_adj, mem_insert]
  aesop

private lemma reachable_fanGraph_source [DecidableEq V] {H : SimpleGraph V}
    {u z : V} {S : Finset V} (h : (fanGraph H u S).Reachable u z) :
    ∃ a ∈ insert u S, H.Reachable a z := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨u, mem_insert_self u S, Reachable.refl u⟩
  | tail hreach hadj ih =>
      rcases ih with ⟨a, ha, har⟩
      rcases hadj with hadj | ⟨hfan, _⟩
      · exact ⟨a, ha, har.trans hadj.reachable⟩
      · rcases hfan with ⟨_, hz⟩ | ⟨hz, _⟩
        · exact ⟨_, mem_insert_of_mem hz, Reachable.refl _⟩
        · exact ⟨u, mem_insert_self u S, hz.symm ▸ Reachable.refl u⟩

private theorem isAcyclic_fanGraph_iff [DecidableEq V] {H : SimpleGraph V}
    {u : V} {S : Finset V} (hH : H.IsAcyclic) (huS : u ∉ S)
    (hnew : ∀ v ∈ S, ¬H.Adj u v) :
    (fanGraph H u S).IsAcyclic ↔
      ∀ ⦃v⦄, v ∈ insert u S → ∀ ⦃w⦄, w ∈ insert u S →
        v ≠ w → ¬H.Reachable v w := by
  induction S using Finset.induction_on with
  | empty =>
      have hempty : fanGraph H u ∅ = H := by
        ext x y
        simp [fanGraph]
      rw [hempty]
      constructor
      · intro _ v hv w hw hvw
        have hv' : v = u := by simpa using hv
        have hw' : w = u := by simpa using hw
        exact (hvw (hv'.trans hw'.symm)).elim
      · exact fun _ => hH
  | @insert v S hvS ih =>
      have huv : u ≠ v := by
        intro huv
        exact huS (huv ▸ mem_insert_self v S)
      have huS' : u ∉ S := fun hu => huS (mem_insert_of_mem hu)
      have hnewv : ¬H.Adj u v := hnew v (mem_insert_self v S)
      have hnewS : ∀ w ∈ S, ¬H.Adj u w :=
        fun w hw => hnew w (mem_insert_of_mem hw)
      have hPrevNew : ¬(fanGraph H u S).Adj u v := by
        simp [fanGraph, hnewv, hvS, huv, huv.symm]
      rw [fanGraph_insert]
      constructor
      · intro hAll
        have hPrev : (fanGraph H u S).IsAcyclic :=
          hAll.anti (by intro x y h; exact Or.inl h)
        have hOld := (ih huS' hnewS).mp hPrev
        have hnreach : ¬(fanGraph H u S).Reachable u v :=
          (isAcyclic_addEdge_iff hPrev huv hPrevNew).mp hAll
        intro x hx y hy hxy
        have old_of_ne {z : V} (hz : z ∈ insert u (insert v S))
            (hzv : z ≠ v) : z ∈ insert u S := by
          rcases mem_insert.mp hz with hzu | hz
          · exact mem_insert.mpr (Or.inl hzu)
          · rcases mem_insert.mp hz with hzv' | hzS
            · exact (hzv hzv').elim
            · exact mem_insert.mpr (Or.inr hzS)
        rcases eq_or_ne x v with rfl | hxv
        · have hyOld : y ∈ insert u S := old_of_ne hy hxy.symm
          intro hvy
          apply hnreach
          have huy : (fanGraph H u S).Reachable u y := by
            rcases mem_insert.mp hyOld with rfl | hyS
            · exact Reachable.refl _
            · exact (show (fanGraph H u S).Adj u y from
                Or.inr ⟨Or.inl ⟨rfl, hyS⟩, by
                  intro huy; subst y; exact huS' hyS⟩).reachable
          exact huy.trans (hvy.symm.mono (by intro a b h; exact Or.inl h))
        · have hxOld : x ∈ insert u S := old_of_ne hx hxv
          rcases eq_or_ne y v with rfl | hyv
          · intro hxvReach
            apply hnreach
            have hux : (fanGraph H u S).Reachable u x := by
              rcases mem_insert.mp hxOld with rfl | hxS
              · exact Reachable.refl _
              · exact (show (fanGraph H u S).Adj u x from
                  Or.inr ⟨Or.inl ⟨rfl, hxS⟩, by
                    intro hux; subst x; exact huS' hxS⟩).reachable
            exact hux.trans (hxvReach.mono (by intro a b h; exact Or.inl h))
          · exact hOld hxOld (by simpa [hyv] using hy) hxy
      · intro hpair
        have hOldPair : ∀ ⦃x⦄, x ∈ insert u S → ∀ ⦃y⦄,
            y ∈ insert u S → x ≠ y → ¬H.Reachable x y := by
          intro x hx y hy hxy
          exact hpair (by aesop) (by aesop) hxy
        have hPrev := (ih huS' hnewS).mpr hOldPair
        apply (isAcyclic_addEdge_iff hPrev huv hPrevNew).mpr
        intro hreach
        obtain ⟨a, ha, hav⟩ := reachable_fanGraph_source hreach
        have havne : a ≠ v := by
          intro havEq
          subst a
          rcases mem_insert.mp ha with huvEq | hvS'
          · exact huv huvEq.symm
          · exact hvS hvS'
        exact hpair (by aesop) (by aesop) havne hav

/-- Neighbors of `u` whose incident edge is newly forced when `u` is inserted. -/
noncomputable def forcedOutsideNeighbors [Fintype V]
    (G : SimpleGraph V) (F : Set V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.Adj u v ∧ v ∉ F

private lemma forcedEdgeGraph_insert_eq_fan [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : Set V}
    {u : V} (hu : u ∉ F) :
    forcedEdgeGraph G (insert u F) =
      fanGraph (forcedEdgeGraph G F) u (forcedOutsideNeighbors G F u) := by
  classical
  ext x y
  simp only [forcedEdgeGraph, fanGraph, forcedOutsideNeighbors, mem_filter,
    mem_univ, true_and, Set.mem_insert_iff]
  constructor
  · rintro ⟨hxy, (rfl | hxF) | (rfl | hyF)⟩
    · by_cases hy : y ∈ F
      · exact Or.inl ⟨hxy, Or.inr hy⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, hxy, hy⟩, G.ne_of_adj hxy⟩
    · exact Or.inl ⟨hxy, Or.inl hxF⟩
    · by_cases hx : x ∈ F
      · exact Or.inl ⟨hxy, Or.inl hx⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, Adj.symm hxy, hx⟩, G.ne_of_adj hxy⟩
    · exact Or.inl ⟨hxy, Or.inr hyF⟩
  · rintro (⟨hxy, hxF | hyF⟩ | ⟨(⟨rfl, huy, hyF⟩ | ⟨rfl, hux, hxF⟩), hne⟩)
    · exact ⟨hxy, Or.inl (Or.inr hxF)⟩
    · exact ⟨hxy, Or.inr (Or.inr hyF)⟩
    · exact ⟨huy, Or.inl (Or.inl rfl)⟩
    · exact ⟨Adj.symm hux, Or.inr (Or.inl rfl)⟩

/-- Exact one-vertex exchange criterion for forced forests.  The attachment
vertices are `u` and its ambient neighbors outside the old forced set. -/
theorem forcedEdgeGraph_insert_isAcyclic_iff [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : Set V}
    {u : V} (hu : u ∉ F)
    (hH : (forcedEdgeGraph G F).IsAcyclic) :
    (forcedEdgeGraph G (insert u F)).IsAcyclic ↔
      ∀ ⦃v⦄, v ∈ ({u} ∪ (G.neighborSet u \ F) : Set V) →
        ∀ ⦃w⦄, w ∈ ({u} ∪ (G.neighborSet u \ F) : Set V) →
          v ≠ w → ¬(forcedEdgeGraph G F).Reachable v w := by
  classical
  rw [forcedEdgeGraph_insert_eq_fan hu]
  have huS : u ∉ forcedOutsideNeighbors G F u := by
    simp [forcedOutsideNeighbors]
  have hnew : ∀ v ∈ forcedOutsideNeighbors G F u,
      ¬(forcedEdgeGraph G F).Adj u v := by
    intro v hv hadj
    simp only [forcedOutsideNeighbors, mem_filter, mem_univ, true_and] at hv
    rcases hadj.2 with huF | hvF
    · exact hu huF
    · exact hv.2 hvF
  rw [isAcyclic_fanGraph_iff hH huS hnew]
  simp only [mem_insert, forcedOutsideNeighbors, mem_filter, mem_univ, true_and,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff, mem_neighborSet]

/-- A forced-acyclic set to which no single vertex can be added. -/
def MaximalForcedAcyclic (G : SimpleGraph V) (F : Set V) : Prop :=
  (forcedEdgeGraph G F).IsAcyclic ∧
    ∀ u, u ∉ F → ¬(forcedEdgeGraph G (insert u F)).IsAcyclic

/-- Maximality means that every omitted vertex has two distinct attachments
which are already reachable from one another in the old forced forest. -/
theorem maximalForcedAcyclic_iff_reachable [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : Set V} :
    MaximalForcedAcyclic G F ↔
      (forcedEdgeGraph G F).IsAcyclic ∧
        ∀ u, u ∉ F →
          ∃ v ∈ ({u} ∪ (G.neighborSet u \ F) : Set V),
            ∃ w ∈ ({u} ∪ (G.neighborSet u \ F) : Set V),
              v ≠ w ∧ (forcedEdgeGraph G F).Reachable v w := by
  classical
  constructor
  · rintro ⟨hH, hmax⟩
    refine ⟨hH, ?_⟩
    intro u hu
    have hfail := hmax u hu
    rw [forcedEdgeGraph_insert_isAcyclic_iff hu hH] at hfail
    push Not at hfail
    exact hfail
  · rintro ⟨hH, hrepeat⟩
    refine ⟨hH, ?_⟩
    intro u hu hins
    rw [forcedEdgeGraph_insert_isAcyclic_iff hu hH] at hins
    obtain ⟨v, hv, w, hw, hvw, hreach⟩ := hrepeat u hu
    exact hins hv hw hvw hreach

/-- The grid extremum is attained by a one-vertex-maximal forced-acyclic set. -/
theorem exists_card_eq_maxForcedAcyclic_and_maximal (m n : Nat) :
    ∃ F : Finset (GridVertex m n),
      F.card = maxForcedAcyclic m n ∧
        MaximalForcedAcyclic (gridGraph m n) (↑F : Set (GridVertex m n)) := by
  classical
  have hnonempty : (acyclicForcedSets m n).Nonempty := by
    refine ⟨∅, mem_acyclicForcedSets.mpr ?_⟩
    have hempty : forcedEdgeGraph (gridGraph m n)
        (↑(∅ : Finset (GridVertex m n)) : Set (GridVertex m n)) = ⊥ := by
      ext x y
      simp [forcedEdgeGraph]
    rw [hempty]
    exact SimpleGraph.isAcyclic_bot
  obtain ⟨F, hF, hsup⟩ :=
    Finset.exists_mem_eq_sup (acyclicForcedSets m n) hnonempty Finset.card
  have hcard : F.card = maxForcedAcyclic m n := by
    exact hsup.symm
  refine ⟨F, hcard, mem_acyclicForcedSets.mp hF, ?_⟩
  intro u hu hins
  have hinsert : insert u F ∈ acyclicForcedSets m n :=
    mem_acyclicForcedSets.mpr (by simpa using hins)
  have hle := Finset.le_sup (f := Finset.card) hinsert
  rw [hsup, card_insert_of_notMem (by simpa using hu)] at hle
  omega

end GridGraphs
