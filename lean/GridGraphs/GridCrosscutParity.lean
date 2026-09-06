import GridGraphs.GridCrosscutCycle
import GridGraphs.GridDual
import GridGraphs.GridEdge

/-!
# Row-ray parity for grid crosscuts

This file packages the local separation consequences of the finite row-ray
argument.  For a simple grid cycle, every coordinate edge on the cycle has
incident faces on opposite parity sides, while every coordinate edge off the
cycle has incident faces on the same side.  Consequently every dual path
disjoint from the cycle preserves side, and a dual path between opposite-side
faces must cross the cycle.

These statements are the parity core needed by a collared-crosscut
construction and use neither planar-embedding infrastructure nor a Jordan
curve theorem.
-/

namespace GridGraphs

open SimpleGraph

/-! ## Cyclic-order arithmetic -/

/-- Distinct offsets shorter than one revolution name distinct cyclic
positions. -/
theorem cyclicOffset_ne_of_lt {k : Nat} (hk : 0 < k) (a : Fin k)
    {s t : Nat} (hs : s < t) (ht : t < k) :
    cyclicOffset hk a s ≠ cyclicOffset hk a t := by
  intro h
  have hsK : s < k := by omega
  have hs' : cyclicOffset hk a s = a + ⟨s, hsK⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  have ht' : cyclicOffset hk a t = a + ⟨t, ht⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  rw [hs', ht'] at h
  have hst : (⟨s, hsK⟩ : Fin k) = ⟨t, ht⟩ := add_left_cancel h
  have := congrArg Fin.val hst
  simp at this
  omega

theorem cyclicForwardDistance_self {k : Nat} (hk : 0 < k) (a : Fin k) :
    cyclicForwardDistance hk a a = 0 := by
  simp [cyclicForwardDistance]

theorem cyclicForwardDistance_offset {k : Nat} (hk : 0 < k) (a : Fin k)
    {t : Nat} (ht : t < k) :
    cyclicForwardDistance hk a (cyclicOffset hk a t) = t := by
  have hoff := cyclicOffset_forwardDistance hk a (cyclicOffset hk a t)
  have hdlt := cyclicForwardDistance_lt hk a (cyclicOffset hk a t)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact cyclicOffset_ne_of_lt hk a hlt ht hoff
  · exact cyclicOffset_ne_of_lt hk a hgt hdlt hoff.symm

/-- Four-place cyclic order is strict increase of clockwise distances from its
first entry. -/
theorem cyclicOrder4_iff_forwardDistance {k : Nat} (hk : 0 < k)
    (a b c d : Fin k) :
    CyclicOrder4 hk a b c d ↔
      0 < cyclicForwardDistance hk a b ∧
      cyclicForwardDistance hk a b < cyclicForwardDistance hk a c ∧
      cyclicForwardDistance hk a c < cyclicForwardDistance hk a d := by
  constructor
  · rintro ⟨p, q, r, hp, hq, hr, hsum, rfl, rfl, rfl⟩
    rw [cyclicForwardDistance_offset hk a (by omega),
      cyclicForwardDistance_offset hk a (by omega),
      cyclicForwardDistance_offset hk a hsum]
    omega
  · rintro ⟨h0b, hbc, hcd⟩
    let db := cyclicForwardDistance hk a b
    let dc := cyclicForwardDistance hk a c
    let dd := cyclicForwardDistance hk a d
    refine ⟨db, dc - db, dd - dc, h0b, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · have := cyclicForwardDistance_lt hk a d
      dsimp [dd]
      omega
    · exact (cyclicOffset_forwardDistance hk a b).symm
    · have hb : db + (dc - db) = dc := by omega
      rw [hb]
      exact (cyclicOffset_forwardDistance hk a c).symm
    · have hb : db + (dc - db) + (dd - dc) = dd := by omega
      rw [hb]
      exact (cyclicOffset_forwardDistance hk a d).symm

/-- The four entries in `CyclicOrder4` are pairwise distinct. -/
theorem CyclicOrder4.pairwise_ne {k : Nat} {hk : 0 < k}
    {a b c d : Fin k} (h : CyclicOrder4 hk a b c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨p, q, r, hp, hq, hr, hsum, rfl, rfl, rfl⟩ := h
  have h0p : 0 < p := hp
  have hpq : p < p + q := by omega
  have hpqr : p + q < p + q + r := by omega
  have hpk : p < k := by omega
  have hpqk : p + q < k := by omega
  have hpqrk : p + q + r < k := hsum
  have ha0 : a = cyclicOffset hk a 0 := by
    apply Fin.ext
    simp [cyclicOffset, Nat.mod_eq_of_lt a.isLt]
  have ha_ne (t : Nat) (ht : 0 < t) (htk : t < k) :
      a ≠ cyclicOffset hk a t := by
    intro h
    exact cyclicOffset_ne_of_lt hk a ht htk (ha0.symm.trans h)
  exact ⟨ha_ne p h0p hpk,
    ha_ne (p + q) (by omega) hpqk,
    ha_ne (p + q + r) (by omega) hpqrk,
    cyclicOffset_ne_of_lt hk a hpq hpqk,
    cyclicOffset_ne_of_lt hk a (by omega) hpqrk,
    cyclicOffset_ne_of_lt hk a hpqr hpqrk⟩

/-- Alternating endpoint pairs consist of four distinct positions. -/
theorem CyclicallyAlternating.pairwise_ne {k : Nat} {hk : 0 < k}
    {a b c d : Fin k} (h : CyclicallyAlternating hk a b c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  rcases h with h | h
  · obtain ⟨hac, hab, had, hcb, hcd, hbd⟩ := h.pairwise_ne
    exact ⟨hab, hac, had, hcb.symm, hbd, hcd⟩
  · obtain ⟨had, hab, hac, hdb, hdc, hbc⟩ := h.pairwise_ne
    exact ⟨hab, hac, had, hbc, hdb.symm, hdc.symm⟩

set_option maxHeartbeats 1000000 in
/-- Alternation is symmetric in the two endpoint pairs. -/
theorem cyclicallyAlternating_swap_pairs {k : Nat} (hk : 0 < k)
    (a b c d : Fin k) :
    CyclicallyAlternating hk a b c d ↔ CyclicallyAlternating hk c d a b := by
  simp only [CyclicallyAlternating, cyclicOrder4_iff_forwardDistance]
  unfold cyclicForwardDistance
  split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 1000000 in
/-- Away from the two cut positions, alternating pairs are exactly pairs in
opposite open cyclic sectors. -/
theorem cyclicallyAlternating_iff_openCyclicSector {k : Nat} (hk : 0 < k)
    (c d x y : Fin k) (hxc : x ≠ c) (hxd : x ≠ d)
    (hyc : y ≠ c) (hyd : y ≠ d) :
    CyclicallyAlternating hk x y c d ↔
      (OpenCyclicSector hk c d x ↔ ¬OpenCyclicSector hk c d y) := by
  simp only [CyclicallyAlternating, cyclicOrder4_iff_forwardDistance]
  unfold OpenCyclicSector cyclicForwardDistance
  split_ifs <;> simp_all <;> omega

/-- The row-ray side of a face relative to a closed grid walk. -/
def GridCycleSide {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (c : G.Walk v v) (f : GridFace m n) : Prop :=
  FaceRowRayOdd c f

@[simp] theorem gridCycleSide_out {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (c : G.Walk v v) : ¬GridCycleSide c GridFace.out :=
  faceRowRayOdd_out c

/-- An odd exclusive-or count says that the two filtered counts have opposite
parity. -/
theorem odd_countP_xor_iff {α : Type*} (l : List α) (p q : α → Bool)
    (hxor : Odd (l.countP fun x => p x != q x)) :
    Odd (l.countP p) ↔ ¬Odd (l.countP q) := by
  have hcount : l.countP p + l.countP q =
      l.countP (fun x => p x != q x) +
        2 * l.countP (fun x => p x && q x) := by
    clear hxor
    induction l with
    | nil => simp
    | cons x l ih =>
        cases hp : p x <;> cases hq : q x <;> simp_all <;> omega
  have hsum : Odd (l.countP p + l.countP q) := by
    rw [hcount]
    exact hxor.add_even (even_two_mul _)
  rw [Nat.odd_add] at hsum
  exact hsum.trans Nat.not_odd_iff_even.symm

/-- The two incident faces of a horizontal cycle edge have opposite row-ray
parity. -/
theorem gridCycleSide_horizontal_iff_not_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : HorizontalGridEdge m n)
    (he : s((horizontalPrimalEndpoints e).1,
      (horizontalPrimalEndpoints e).2) ∈ c.edges) :
    GridCycleSide c (horizontalDualEndpoints e).1 ↔
      ¬GridCycleSide c (horizontalDualEndpoints e).2 := by
  simp only [GridCycleSide]
  rw [faceRowRayOdd_iff_odd_countP hc.isTrail,
    faceRowRayOdd_iff_odd_countP hc.isTrail]
  apply odd_countP_xor_iff
  let target := s((horizontalPrimalEndpoints e).1,
    (horizontalPrimalEndpoints e).2)
  let p := fun x =>
    FaceRowRayCrossesEdge (horizontalDualEndpoints e).1 x !=
      FaceRowRayCrossesEdge (horizontalDualEndpoints e).2 x
  let q := EdgeCrossesBoolCut (gridHorizontalSegmentSide e.row e.col)
  have hp : p target = false := by
    have hface (f : GridFace m n) : FaceRowRayCrossesEdge f target = false := by
      cases f with
      | out => rfl
      | cell row col => exact edgeCrossesRowRay_horizontal row col e
    simp [p, hface]
  have hq : q target = true := by
    exact (horizontal_edge_crosses_horizontalSegment_iff e.row e.col e).mpr
      ⟨rfl, rfl⟩
  have heq : ∀ x ∈ c.edges, x ≠ target → p x = q x := by
    intro edge hedge hne
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hadj := hG (c.adj_of_mem_edges hedge)
        rcases gridGraph_adj_exists_coordinate_edge hadj with h | h
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · simpa [p, q, target] using
              horizontalDual_rowRay_xor_on_horizontal_edge e a hne
          · rw [Sym2.eq_swap]
            simpa [p, q, target, Sym2.eq_swap] using
              horizontalDual_rowRay_xor_on_horizontal_edge e a
                (by simpa only [Sym2.eq_swap] using hne)
        · obtain ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
          · simpa [p, q] using horizontalDual_rowRay_xor_on_vertical_edge e a
          · simpa [p, q, Sym2.eq_swap] using
              horizontalDual_rowRay_xor_on_vertical_edge e a
  have hdiff : c.edges.countP p + 1 = c.edges.countP q :=
    List.countP_add_one_eq_of_eq_except c.edges target p q
      hc.isTrail.edges_nodup he hp hq heq
  have hqeven : Even (c.edges.countP q) := by
    rw [← walkCutCrossings_eq_countP_edges]
    exact even_walkCutCrossings_of_isClosed _ c
  rw [← hdiff] at hqeven
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hqeven)

/-- The two incident faces of a vertical cycle edge have opposite row-ray
parity. -/
theorem gridCycleSide_vertical_iff_not_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : VerticalGridEdge m n)
    (he : s((verticalPrimalEndpoints e).1,
      (verticalPrimalEndpoints e).2) ∈ c.edges) :
    GridCycleSide c (verticalDualEndpoints e).1 ↔
      ¬GridCycleSide c (verticalDualEndpoints e).2 := by
  simp only [GridCycleSide]
  by_cases hleft : e.col.val = 0
  · by_cases hright : e.col.val + 1 = n
    · have hfull := even_rowCrossingEdges_card hG c hc.isTrail e.row
      have hsingleton : rowCrossingEdges c e.row = {e} := by
        ext a
        simp only [mem_rowCrossingEdges_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨_, har⟩
          apply verticalGridEdge_eq_of_row_eq_of_col_val_eq har
          omega
        · rintro rfl
          exact ⟨he, rfl⟩
      rw [hsingleton] at hfull
      simp at hfull
    · rw [show (verticalDualEndpoints e).1 = GridFace.out by
          simp [verticalDualEndpoints, hleft],
        show (verticalDualEndpoints e).2 =
            GridFace.cell e.row ⟨0, by omega⟩ by
          have hn : 1 ≠ n := by omega
          simp [verticalDualEndpoints, hleft, hn]]
      simp only [FaceRowRayOdd, false_iff, not_not]
      rw [rowRayCrossingEdges_left_eq_singleton_of_mem_edges
        c e hleft hright he]
      simp
  · by_cases hright : e.col.val + 1 = n
    · rw [show (verticalDualEndpoints e).1 =
            GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
          simp [verticalDualEndpoints, hleft],
        show (verticalDualEndpoints e).2 = GridFace.out by
          simp [verticalDualEndpoints, hright]]
      simp only [FaceRowRayOdd, not_false_eq_true, iff_true]
      have hfull := even_rowCrossingEdges_card hG c hc.isTrail e.row
      rw [rowCrossingEdges_eq_insert_rightPrefix_of_right_boundary
        c e hleft hright he, Finset.card_insert_of_notMem] at hfull
      · exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hfull)
      · simp only [mem_rowRayCrossingEdges_iff, not_and_or]
        right
        right
        omega
    · rw [show (verticalDualEndpoints e).1 =
            GridFace.cell e.row ⟨e.col.val - 1, by omega⟩ by
          simp [verticalDualEndpoints, hleft],
        show (verticalDualEndpoints e).2 =
            GridFace.cell e.row ⟨e.col.val, by omega⟩ by
          simp [verticalDualEndpoints, hright]]
      simp only [FaceRowRayOdd]
      rw [rowRayCrossingEdges_right_eq_insert_of_mem_edges
        c e hleft hright he, Finset.card_insert_of_notMem]
      · rw [Nat.odd_add_one]
        simp
      · simp only [mem_rowRayCrossingEdges_iff, not_and_or]
        right
        right
        omega

/-- A coordinate edge on a simple grid cycle toggles row-ray side. -/
theorem gridCycleSide_dualEndpoints_iff_not_of_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : GridEdge m n) (he : e.primalSym2 ∈ c.edges) :
    GridCycleSide c e.dualEndpoints.1 ↔
      ¬GridCycleSide c e.dualEndpoints.2 := by
  cases e with
  | horizontal e => exact gridCycleSide_horizontal_iff_not_of_mem_edges hG c hc e he
  | vertical e => exact gridCycleSide_vertical_iff_not_of_mem_edges hG c hc e he

/-- A coordinate edge absent from a simple grid cycle preserves row-ray side. -/
theorem gridCycleSide_dualEndpoints_iff_of_not_mem_edges {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) (e : GridEdge m n) (he : e.primalSym2 ∉ c.edges) :
    GridCycleSide c e.dualEndpoints.1 ↔
      GridCycleSide c e.dualEndpoints.2 := by
  cases e with
  | horizontal e =>
      exact faceRowRayOdd_horizontal_iff_of_not_mem_edges hG c hc e he
  | vertical e =>
      by_cases hleft : e.col.val = 0
      · exact faceRowRayOdd_vertical_left_iff_of_not_mem_edges c e hleft he
      · by_cases hright : e.col.val + 1 = n
        · exact faceRowRayOdd_vertical_right_iff_of_not_mem_edges
            hG c hc.isTrail e hleft hright he
        · exact faceRowRayOdd_vertical_internal_iff_of_not_mem_edges
            c e hleft hright he

/-- The bounded face incident to an outer-frame edge is on the odd side of a
simple cycle exactly when that boundary edge belongs to the cycle. -/
theorem gridCycleSide_outerEdgeInnerFace_iff_mem_edges {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {G : SimpleGraph (GridVertex (m + 2) (n + 2))}
    {v : GridVertex (m + 2) (n + 2)} (c : G.Walk v v)
    (hG : G ≤ gridGraph (m + 2) (n + 2)) (hc : c.IsCycle)
    (i : GridBoundaryPosition m n) :
    GridCycleSide c (outerEdgeInnerFace hm hn i) ↔
      (outerEdgeAtPosition hm hn i).primalSym2 ∈ c.edges := by
  let e := outerEdgeAtPosition hm hn i
  have hends : HasDualEndpoints e.dualEndpoints GridFace.out
      (outerEdgeInnerFace hm hn i) :=
    outerEdgeAtPosition_hasDualEndpoints_out_innerFace hm hn i
  by_cases he : e.primalSym2 ∈ c.edges
  · have htoggle := gridCycleSide_dualEndpoints_iff_not_of_mem_edges hG c hc e he
    rcases hends with ⟨hout, hin⟩ | ⟨hout, hin⟩
    · rw [← hout, ← hin] at htoggle
      simp only [gridCycleSide_out, false_iff, not_not] at htoggle
      exact ⟨fun _ => he, fun _ => htoggle⟩
    · rw [← hout, ← hin] at htoggle
      simp only [gridCycleSide_out, not_false_eq_true, iff_true] at htoggle
      exact ⟨fun _ => he, fun _ => htoggle⟩
  · have hsame := gridCycleSide_dualEndpoints_iff_of_not_mem_edges hG c hc e he
    rcases hends with ⟨hout, hin⟩ | ⟨hout, hin⟩
    · rw [← hout, ← hin] at hsame
      simp only [gridCycleSide_out, false_iff] at hsame
      exact ⟨fun h => (hsame h).elim, fun h => (he h).elim⟩
    · rw [← hout, ← hin] at hsame
      simp only [gridCycleSide_out, iff_false] at hsame
      exact ⟨fun h => (hsame h).elim, fun h => (he h).elim⟩

/-- A non-endpoint outer edge belongs to the clockwise canonical closure
exactly when its original boundary position lies in the open clockwise sector
between the crosscut endpoints. -/
theorem outerEdgeAtPosition_mem_canonicalClosedWalk_clockwise_iff_openCyclicSector
    {m n : Nat} (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n)
    (his : i ≠ P.startPosition hm hn)
    (hif : i ≠ P.finishPosition hm hn) :
    (outerEdgeAtPosition hm hn i).primalSym2 ∈
        (P.canonicalClosedWalk .clockwise hm hn).edges ↔
      OpenCyclicSector (gridBoundaryLength_pos hm hn)
        (P.startPosition hm hn) (P.finishPosition hm hn) i := by
  rw [P.outerEdgeAtPosition_mem_canonicalClosedWalk_clockwise_iff_outerArc hm hn i]
  exact outerEdgeAtPosition_mem_clockwiseOuterArc_iff_openCyclicSector hm hn
    (P.startPosition hm hn) (P.finishPosition hm hn) i
    (fun h => P.start_ne_finish (by
      rw [← P.boundaryVertex_startPosition hm hn,
        ← P.boundaryVertex_finishPosition hm hn, h])) his hif

/-- The bounded face beside a non-endpoint outer edge is on the canonical
clockwise cycle side exactly on the corresponding open boundary sector. -/
theorem gridCycleSide_outerEdgeInnerFace_clockwise_iff_openCyclicSector
    {m n : Nat} (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n)
    (his : i ≠ P.startPosition hm hn)
    (hif : i ≠ P.finishPosition hm hn) :
    GridCycleSide (P.canonicalClosedWalk .clockwise hm hn)
        (outerEdgeInnerFace hm hn i) ↔
      OpenCyclicSector (gridBoundaryLength_pos hm hn)
        (P.startPosition hm hn) (P.finishPosition hm hn) i := by
  rw [gridCycleSide_outerEdgeInnerFace_iff_mem_edges hm hn
    (P.canonicalClosedWalk .clockwise hm hn) (fun _ _ h => h)
    (P.canonicalClosedWalk_isCycle .clockwise hm hn) i]
  exact outerEdgeAtPosition_mem_canonicalClosedWalk_clockwise_iff_openCyclicSector
    P hm hn i his hif

/-- Every path in the dual complement of a simple grid cycle preserves
row-ray side. -/
theorem gridCycleSide_reachable_iff {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) {f g : GridFace m n}
    (hfg : (cycleComplementDualGraph c).Reachable f g) :
    GridCycleSide c f ↔ GridCycleSide c g := by
  let hh := fun e he => faceRowRayOdd_horizontal_iff_of_not_mem_edges hG c hc e he
  let hv := fun (e : VerticalGridEdge m n) he => by
    by_cases hleft : e.col.val = 0
    · exact faceRowRayOdd_vertical_left_iff_of_not_mem_edges c e hleft he
    · by_cases hright : e.col.val + 1 = n
      · exact faceRowRayOdd_vertical_right_iff_of_not_mem_edges
          hG c hc.isTrail e hleft hright he
      · exact faceRowRayOdd_vertical_internal_iff_of_not_mem_edges
          c e hleft hright he
  exact reachable_mem_iff_of_respectsCut
    (cycleComplementDualGraph_respects_faceRowRayOdd c hh hv) hfg

/-- Opposite row-ray sides cannot be joined without crossing a cycle edge. -/
theorem not_cycleComplementDualGraph_reachable_of_opposite_side {m n : Nat}
    {G : SimpleGraph (GridVertex m n)} {v : GridVertex m n}
    (hG : G ≤ gridGraph m n) (c : G.Walk v v)
    (hc : c.IsCycle) {f g : GridFace m n}
    (hopposite : GridCycleSide c f ↔ ¬GridCycleSide c g) :
    ¬(cycleComplementDualGraph c).Reachable f g := by
  intro hfg
  have hsame := gridCycleSide_reachable_iff hG c hc hfg
  by_cases hf : GridCycleSide c f
  · exact (hopposite.mp hf) (hsame.mp hf)
  · exact hf (hsame.mpr ((not_not.mp (hopposite.not.mp hf))))

/-! ## Primal paths in the central rectangle -/

/-- The northwest unit face incident to the translated copy of a grid vertex. -/
def gridCollarFace {m n : Nat} (x : GridVertex m n) :
    GridFace (m + 2) (n + 2) :=
  .cell ⟨x.1.val, by omega⟩ ⟨x.2.val, by omega⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- For a non-endpoint boundary position, the bounded face beside its outgoing
outer edge is connected through the collar to the northwest anchor face of the
original boundary vertex.  The path has zero, one, or two dual edges according
to the boundary side. -/
theorem outerEdgeInnerFace_reachable_gridCollarFace_clockwise
    {m n : Nat} (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n)
    (his : i ≠ P.startPosition hm hn)
    (hif : i ≠ P.finishPosition hm hn) :
    (cycleComplementDualGraph (P.canonicalClosedWalk .clockwise hm hn)).Reachable
      (outerEdgeInnerFace hm hn i)
      (gridCollarFace (gridBoundaryVertex hm hn i)) := by
  let c := P.canonicalClosedWalk .clockwise hm hn
  let x := gridBoundaryVertex hm hn i
  have hx : gridCollarEmbedding m n x ∉ c.support := by
    rw [P.mem_canonicalClosedWalk_of_original_boundary_iff .clockwise hm hn x
      (gridBoundaryVertex_isBoundary hm hn i)]
    push Not
    constructor
    · intro h
      apply his
      apply gridBoundaryVertex_injective hm hn
      simpa [x, P.boundaryVertex_startPosition hm hn] using h
    · intro h
      apply hif
      apply gridBoundaryVertex_injective hm hn
      simpa [x, P.boundaryVertex_finishPosition hm hn] using h
  have hi := i.isLt
  unfold gridBoundaryLength at hi
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hmsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hrightStart : n + m - 2 = (n - 1) + (m - 1) := by omega
  have hbottomStart : m + 2 * n - 3 = (n + m - 2) + (n - 1) := by omega
  have hboundaryLength : gridBoundaryLength m n =
      (m + 2 * n - 3) + (m - 1) := by
    unfold gridBoundaryLength
    omega
  by_cases htop : i.val < n - 1
  · let e : VerticalGridEdge (m + 2) (n + 2) :=
      ⟨⟨0, by omega⟩, ⟨i.val + 1, by omega⟩⟩
    have hibound : i.val < m + 2 * n - 3 := by
      rw [hbottomStart, hrightStart]
      omega
    have hxcoord : gridBoundaryVertex hm hn i =
        (⟨0, by omega⟩, ⟨i.val, by omega⟩) := by
      exact gridBoundaryVertex_top hm hn i (by omega)
    apply SimpleGraph.Adj.reachable
    refine ⟨?_, Or.inr ⟨e, ?_, ?_⟩⟩
    · intro h
      have hc := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell _ col => col.val) h
      rw [outerEdgeInnerFace_eq_top hm hn i htop] at hc
      simp [gridCollarFace, hxcoord] at hc
    · intro he
      apply hx
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (verticalPrimalEndpoints e).2 = gridCollarEmbedding m n x := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, x, hxcoord, verticalPrimalEndpoints]
      exact hend ▸ hs
    · right
      rw [outerEdgeInnerFace_eq_top hm hn i htop]
      simp [gridCollarFace, hxcoord, e, verticalDualEndpoints]
      omega
  by_cases hright : i.val < n + m - 2
  · let r := i.val + 1 - n
    have hrcoord : i.val + 2 - n = r + 1 := by
      dsimp [r]
      omega
    have hibound : i.val < m + 2 * n - 3 := by
      rw [hbottomStart]
      omega
    have hxcoord : gridBoundaryVertex hm hn i =
        (⟨r, by omega⟩, ⟨n - 1, by omega⟩) := by
      dsimp [r]
      unfold gridBoundaryVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
    let fmid : GridFace (m + 2) (n + 2) :=
      .cell ⟨r, by omega⟩ ⟨n, by omega⟩
    let e₁ : HorizontalGridEdge (m + 2) (n + 2) :=
      ⟨⟨r + 1, by omega⟩, ⟨n, by omega⟩⟩
    let e₂ : VerticalGridEdge (m + 2) (n + 2) :=
      ⟨⟨r, by omega⟩, ⟨n, by omega⟩⟩
    have h₁ : (cycleComplementDualGraph c).Adj
        (outerEdgeInnerFace hm hn i) fmid := by
      refine ⟨?_, Or.inl ⟨e₁, ?_, ?_⟩⟩
      · rw [outerEdgeInnerFace_eq_right hm hn i htop hright]
        simp [fmid, r, hrcoord, Fin.ext_iff]
      · intro he
        apply hx
        have hs := c.fst_mem_support_of_mem_edges he
        have hend : (horizontalPrimalEndpoints e₁).1 =
            gridCollarEmbedding m n x := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [e₁, r, x, hxcoord, horizontalPrimalEndpoints, hnsub]
        exact hend ▸ hs
      · right
        rw [outerEdgeInnerFace_eq_right hm hn i htop hright]
        simp [fmid, e₁, r, hrcoord, horizontalDualEndpoints]
        omega
    have h₂ : (cycleComplementDualGraph c).Adj fmid
        (gridCollarFace x) := by
      refine ⟨?_, Or.inr ⟨e₂, ?_, ?_⟩⟩
      · simp [fmid, gridCollarFace, x, hxcoord,
          r, Fin.ext_iff]
        omega
      · intro he
        apply hx
        have hs := c.snd_mem_support_of_mem_edges he
        have hend : (verticalPrimalEndpoints e₂).2 =
            gridCollarEmbedding m n x := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [e₂, r, x, hxcoord, verticalPrimalEndpoints, hnsub]
        exact hend ▸ hs
      · right
        simp [fmid, gridCollarFace, x, hxcoord,
          e₂, r, verticalDualEndpoints]
        omega
    exact h₁.reachable.trans h₂.reachable
  by_cases hbottom : i.val < m + 2 * n - 3
  · let q := m + 2 * n - 3 - i.val
    have hibound : i.val < gridBoundaryLength m n := by
      calc
        i.val < m + 2 * n - 3 := hbottom
        _ ≤ gridBoundaryLength m n := by
          rw [hboundaryLength]
          omega
    have hxcoord : gridBoundaryVertex hm hn i =
        (⟨m - 1, by omega⟩, ⟨q, by omega⟩) := by
      dsimp [q]
      unfold gridBoundaryVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
    let e : HorizontalGridEdge (m + 2) (n + 2) :=
      ⟨⟨m, by omega⟩, ⟨q, by omega⟩⟩
    apply SimpleGraph.Adj.reachable
    refine ⟨?_, Or.inl ⟨e, ?_, ?_⟩⟩
    · intro h
      have hr := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell row _ => row.val) h
      rw [outerEdgeInnerFace_eq_bottom hm hn i hright hbottom] at hr
      simp [gridCollarFace, hxcoord, q] at hr
      omega
    · intro he
      apply hx
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (horizontalPrimalEndpoints e).2 = gridCollarEmbedding m n x := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, q, x, hxcoord, horizontalPrimalEndpoints, hmsub]
      exact hend ▸ hs
    · right
      rw [outerEdgeInnerFace_eq_bottom hm hn i hright hbottom]
      simp [gridCollarFace, hxcoord, e, q, horizontalDualEndpoints]
      omega
  · have hxcoord : gridBoundaryVertex hm hn i =
        (⟨gridBoundaryLength m n - i.val, by
          unfold gridBoundaryLength
          omega⟩, ⟨0, by omega⟩) := by
      unfold gridBoundaryVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;>
        simp_all [gridBoundaryLength] <;> omega
    have heq : outerEdgeInnerFace hm hn i = gridCollarFace x := by
      rw [outerEdgeInnerFace_eq_left hm hn i hbottom]
      simp [gridCollarFace, x, hxcoord]
    rw [heq]

/-- The northwest anchor face at a non-endpoint boundary vertex has canonical
clockwise side precisely on the open clockwise endpoint sector. -/
theorem gridCycleSide_gridCollarFace_clockwise_iff_openCyclicSector
    {m n : Nat} (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n)
    (his : i ≠ P.startPosition hm hn)
    (hif : i ≠ P.finishPosition hm hn) :
    GridCycleSide (P.canonicalClosedWalk .clockwise hm hn)
        (gridCollarFace (gridBoundaryVertex hm hn i)) ↔
      OpenCyclicSector (gridBoundaryLength_pos hm hn)
        (P.startPosition hm hn) (P.finishPosition hm hn) i := by
  rw [← gridCycleSide_outerEdgeInnerFace_clockwise_iff_openCyclicSector
    P hm hn i his hif]
  exact (gridCycleSide_reachable_iff (fun _ _ h => h)
    (P.canonicalClosedWalk .clockwise hm hn)
    (P.canonicalClosedWalk_isCycle .clockwise hm hn)
    (outerEdgeInnerFace_reachable_gridCollarFace_clockwise
      P hm hn i his hif)).symm

/-- Adjacent central vertices have adjacent anchor faces in the dual complement
of any cycle avoiding the translated vertices. -/
theorem cycleComplementDualGraph_adj_gridCollarFace {m n : Nat}
    {G : SimpleGraph (GridVertex (m + 2) (n + 2))} {z : GridVertex (m + 2) (n + 2)}
    (c : G.Walk z z) {x y : GridVertex m n} (hxy : (gridGraph m n).Adj x y)
    (hx : gridCollarEmbedding m n x ∉ c.support)
    (hy : gridCollarEmbedding m n y ∉ c.support) :
    (cycleComplementDualGraph c).Adj (gridCollarFace x) (gridCollarFace y) := by
  rcases hxy with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
  · let e : VerticalGridEdge (m + 2) (n + 2) :=
      ⟨⟨x.1.val, by omega⟩, ⟨y.2.val, by omega⟩⟩
    refine ⟨by
      intro h
      have hc := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell _ col => col.val + 1) h
      simp [gridCollarFace] at hc
      omega, Or.inr ⟨e, ?_, ?_⟩⟩
    · intro he
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (verticalPrimalEndpoints e).2 = gridCollarEmbedding m n x := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, verticalPrimalEndpoints, hrow, hcol]
      exact hx (hend ▸ hs)
    · left
      have hy0 : y.2.val ≠ 0 := by omega
      have hyr : y.2.val ≠ n + 1 := by omega
      constructor
      · simp [gridCollarFace, e, verticalDualEndpoints, hy0, Fin.ext_iff]
        omega
      · simp [gridCollarFace, e, verticalDualEndpoints, hyr, Fin.ext_iff]
        omega
  · let e : VerticalGridEdge (m + 2) (n + 2) :=
      ⟨⟨y.1.val, by omega⟩, ⟨x.2.val, by omega⟩⟩
    refine ⟨by
      intro h
      have hc := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell _ col => col.val + 1) h
      simp [gridCollarFace] at hc
      omega, Or.inr ⟨e, ?_, ?_⟩⟩
    · intro he
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (verticalPrimalEndpoints e).2 = gridCollarEmbedding m n y := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, verticalPrimalEndpoints, hcol]
      exact hy (hend ▸ hs)
    · right
      have hx0 : x.2.val ≠ 0 := by omega
      have hxr : x.2.val ≠ n + 1 := by omega
      constructor
      · simp [gridCollarFace, e, verticalDualEndpoints, hxr, Fin.ext_iff]
        omega
      · simp [gridCollarFace, e, verticalDualEndpoints, hx0, Fin.ext_iff]
        omega
  · let e : HorizontalGridEdge (m + 2) (n + 2) :=
      ⟨⟨y.1.val, by omega⟩, ⟨x.2.val, by omega⟩⟩
    refine ⟨by
      intro h
      have hr := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell row _ => row.val + 1) h
      simp [gridCollarFace] at hr
      omega, Or.inl ⟨e, ?_, ?_⟩⟩
    · intro he
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (horizontalPrimalEndpoints e).2 = gridCollarEmbedding m n x := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, horizontalPrimalEndpoints, hrow, hcol]
      exact hx (hend ▸ hs)
    · left
      have hy0 : y.1.val ≠ 0 := by omega
      have hyr : y.1.val ≠ m + 1 := by omega
      constructor
      · simp [gridCollarFace, e, horizontalDualEndpoints, hy0, Fin.ext_iff]
        omega
      · simp [gridCollarFace, e, horizontalDualEndpoints, hyr, Fin.ext_iff]
        omega
  · let e : HorizontalGridEdge (m + 2) (n + 2) :=
      ⟨⟨x.1.val, by omega⟩, ⟨y.2.val, by omega⟩⟩
    refine ⟨by
      intro h
      have hr := congrArg (fun f => match f with
        | GridFace.out => 0
        | GridFace.cell row _ => row.val + 1) h
      simp [gridCollarFace] at hr
      omega, Or.inl ⟨e, ?_, ?_⟩⟩
    · intro he
      have hs := c.snd_mem_support_of_mem_edges he
      have hend : (horizontalPrimalEndpoints e).2 = gridCollarEmbedding m n y := by
        apply Prod.ext <;> apply Fin.ext <;>
          simp [e, horizontalPrimalEndpoints, hrow]
      exact hy (hend ▸ hs)
    · right
      have hx0 : x.1.val ≠ 0 := by omega
      have hxr : x.1.val ≠ m + 1 := by omega
      constructor
      · simp [gridCollarFace, e, horizontalDualEndpoints, hxr, Fin.ext_iff]
        omega
      · simp [gridCollarFace, e, horizontalDualEndpoints, hx0, Fin.ext_iff]
        omega

/-- A primal walk avoiding a collared cycle gives dual-complement reachability
between the anchor faces of its endpoints. -/
theorem gridCollarFace_reachable_of_walk_disjoint {m n : Nat}
    {G : SimpleGraph (GridVertex (m + 2) (n + 2))} {z : GridVertex (m + 2) (n + 2)}
    (c : G.Walk z z) {x y : GridVertex m n} (q : (gridGraph m n).Walk x y)
    (hdisjoint : ∀ w ∈ q.support, gridCollarEmbedding m n w ∉ c.support) :
    (cycleComplementDualGraph c).Reachable (gridCollarFace x) (gridCollarFace y) := by
  induction q with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x w y hxw q ih =>
      exact (cycleComplementDualGraph_adj_gridCollarFace c hxw
        (hdisjoint x (by simp)) (hdisjoint w (by simp))).reachable.trans
        (ih (fun u hu => hdisjoint u (by simp [hu])))

/-- A primal walk disjoint from a simple collared cycle preserves row-ray side
at its endpoint anchor faces. -/
theorem gridCycleSide_gridCollarFace_iff_of_walk_disjoint {m n : Nat}
    {z : GridVertex (m + 2) (n + 2)}
    (c : (gridGraph (m + 2) (n + 2)).Walk z z) (hc : c.IsCycle)
    {x y : GridVertex m n} (q : (gridGraph m n).Walk x y)
    (hdisjoint : ∀ w ∈ q.support, gridCollarEmbedding m n w ∉ c.support) :
    GridCycleSide c (gridCollarFace x) ↔ GridCycleSide c (gridCollarFace y) := by
  exact gridCycleSide_reachable_iff (fun _ _ h => h) c hc
    (gridCollarFace_reachable_of_walk_disjoint c q hdisjoint)

/-- A walk vertex-disjoint from a proper crosscut preserves side for either
canonical collar closure. -/
theorem GridCrosscut.gridCycleSide_iff_of_walk_disjoint {m n : Nat}
    (P : GridCrosscut m n) (choice : GridCollarArc.CanonicalChoice)
    (hm : 2 ≤ m) (hn : 2 ≤ n) {x y : GridVertex m n}
    (q : (gridGraph m n).Walk x y)
    (hdisjoint : ¬∃ w, w ∈ P.path.support ∧ w ∈ q.support) :
    GridCycleSide (P.canonicalClosedWalk choice hm hn) (gridCollarFace x) ↔
      GridCycleSide (P.canonicalClosedWalk choice hm hn) (gridCollarFace y) := by
  apply gridCycleSide_gridCollarFace_iff_of_walk_disjoint
    (P.canonicalClosedWalk choice hm hn)
    (P.canonicalClosedWalk_isCycle choice hm hn) q
  intro w hw hcycle
  apply hdisjoint
  exact ⟨w, (P.mem_canonicalClosedWalk_collar_iff choice hm hn w).mp hcycle, hw⟩

/-! ## Trimming boundary contacts -/

/-- A simple path whose boundary endpoints have different sector labels
contains a proper crosscut subpath with differently labelled endpoints.  The
crosscut endpoints are consecutive boundary contacts of the original path. -/
theorem exists_gridCrosscut_subpath_of_boundary_sectors {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (sector : GridBoundaryPosition m n → Prop)
    {u v : GridVertex m n} (p : (gridGraph m n).Walk u v) (hp : p.IsPath)
    (hu : IsGridBoundary u) (hv : IsGridBoundary v) (huv : u ≠ v)
    (hopposite :
      sector ((gridBoundaryEquiv hm hn).symm ⟨u, hu⟩) ↔
        ¬sector ((gridBoundaryEquiv hm hn).symm ⟨v, hv⟩)) :
    ∃ P : GridCrosscut m n,
      (∀ ⦃x⦄, x ∈ P.path.support → x ∈ p.support) ∧
      (sector (P.startPosition hm hn) ↔
        ¬sector (P.finishPosition hm hn)) := by
  classical
  by_cases hinter : ∃ z ∈ p.support,
      IsGridBoundary z ∧ z ≠ u ∧ z ≠ v
  · obtain ⟨z, hzp, hzB, hzu, hzv⟩ := hinter
    let zi : GridBoundaryPosition m n :=
      (gridBoundaryEquiv hm hn).symm ⟨z, hzB⟩
    by_cases hsame : sector zi ↔
        sector ((gridBoundaryEquiv hm hn).symm ⟨u, hu⟩)
    · have hside : sector zi ↔
          ¬sector ((gridBoundaryEquiv hm hn).symm ⟨v, hv⟩) :=
        hsame.trans hopposite
      obtain ⟨P, hPsub, hPside⟩ :=
        exists_gridCrosscut_subpath_of_boundary_sectors hm hn sector
          (p.dropUntil z hzp) (hp.dropUntil hzp) hzB hv hzv hside
      refine ⟨P, ?_, hPside⟩
      intro x hx
      exact p.support_dropUntil_subset_support hzp (hPsub hx)
    · have hside : sector ((gridBoundaryEquiv hm hn).symm ⟨u, hu⟩) ↔
          ¬sector zi := by tauto
      obtain ⟨P, hPsub, hPside⟩ :=
        exists_gridCrosscut_subpath_of_boundary_sectors hm hn sector
          (p.takeUntil z hzp) (hp.takeUntil hzp) hu hzB hzu.symm hside
      refine ⟨P, ?_, hPside⟩
      intro x hx
      exact p.support_takeUntil_subset_support hzp (hPsub hx)
  ·
    let P : GridCrosscut m n :=
      { start := u
        finish := v
        path := p
        isPath := hp
        start_ne_finish := huv
        start_boundary := hu
        finish_boundary := hv
        boundary_contact := by
          intro z hzp hzB
          by_cases hzu : z = u
          · exact Or.inl hzu
          · by_cases hzv : z = v
            · exact Or.inr hzv
            · exact (hinter ⟨z, hzp, hzB, hzu, hzv⟩).elim }
    refine ⟨P, ?_, ?_⟩
    · intro x hx
      exact hx
    · simpa [P, GridCrosscut.startPosition, GridCrosscut.finishPosition]
        using hopposite
termination_by p.length
decreasing_by
  · have htake : 0 < (p.takeUntil z hzp).length := by
      rw [Nat.pos_iff_ne_zero]
      intro hzero
      have hnil : (p.takeUntil z hzp).Nil := by
        exact Walk.length_eq_zero_iff.mp hzero
      exact hzu ((p.nil_takeUntil hzp).mp hnil).symm
    have hlen := congrArg Walk.length (p.take_spec hzp)
    rw [Walk.length_append] at hlen
    omega
  · exact p.length_takeUntil_lt_length hzp hzv

/-- Direct trimming for alternating endpoints when the path avoids the other
pair, as it does under a putative disjointness counterexample. -/
theorem exists_gridCrosscut_subpath_preserving_alternation
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a b c d : GridBoundaryPosition m n}
    (p : (gridGraph m n).Walk (gridBoundaryVertex hm hn a)
      (gridBoundaryVertex hm hn b)) (hp : p.IsPath)
    (halt : CyclicallyAlternating (gridBoundaryLength_pos hm hn) a b c d)
    (hcavoid : gridBoundaryVertex hm hn c ∉ p.support)
    (hdavoid : gridBoundaryVertex hm hn d ∉ p.support) :
    ∃ P : GridCrosscut m n,
      (∀ ⦃x⦄, x ∈ P.path.support → x ∈ p.support) ∧
      CyclicallyAlternating (gridBoundaryLength_pos hm hn)
        (P.startPosition hm hn) (P.finishPosition hm hn) c d := by
  let sector := OpenCyclicSector (gridBoundaryLength_pos hm hn) c d
  have hne := halt.pairwise_ne
  have hsectorAB : sector a ↔ ¬sector b :=
    (cyclicallyAlternating_iff_openCyclicSector
      (gridBoundaryLength_pos hm hn) c d a b hne.2.1 hne.2.2.1
        hne.2.2.2.1 hne.2.2.2.2.1).mp halt
  have haPos : (gridBoundaryEquiv hm hn).symm
      ⟨gridBoundaryVertex hm hn a, gridBoundaryVertex_isBoundary hm hn a⟩ = a := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  have hbPos : (gridBoundaryEquiv hm hn).symm
      ⟨gridBoundaryVertex hm hn b, gridBoundaryVertex_isBoundary hm hn b⟩ = b := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  obtain ⟨P, hsub, hPsector⟩ :=
    exists_gridCrosscut_subpath_of_boundary_sectors hm hn sector p hp
      (gridBoundaryVertex_isBoundary hm hn a)
      (gridBoundaryVertex_isBoundary hm hn b)
      (fun h => hne.1 (gridBoundaryVertex_injective hm hn h))
      (by simpa [haPos, hbPos] using hsectorAB)
  have hstart_ne_c : P.startPosition hm hn ≠ c := by
    intro h
    apply hcavoid
    have hv : P.start = gridBoundaryVertex hm hn c := by
      rw [← P.boundaryVertex_startPosition hm hn, h]
    rw [← hv]
    exact hsub P.path.start_mem_support
  have hstart_ne_d : P.startPosition hm hn ≠ d := by
    intro h
    apply hdavoid
    have hv : P.start = gridBoundaryVertex hm hn d := by
      rw [← P.boundaryVertex_startPosition hm hn, h]
    rw [← hv]
    exact hsub P.path.start_mem_support
  have hfinish_ne_c : P.finishPosition hm hn ≠ c := by
    intro h
    apply hcavoid
    have hv : P.finish = gridBoundaryVertex hm hn c := by
      rw [← P.boundaryVertex_finishPosition hm hn, h]
    rw [← hv]
    exact hsub P.path.end_mem_support
  have hfinish_ne_d : P.finishPosition hm hn ≠ d := by
    intro h
    apply hdavoid
    have hv : P.finish = gridBoundaryVertex hm hn d := by
      rw [← P.boundaryVertex_finishPosition hm hn, h]
    rw [← hv]
    exact hsub P.path.end_mem_support
  exact ⟨P, hsub, (cyclicallyAlternating_iff_openCyclicSector
    (gridBoundaryLength_pos hm hn) c d _ _ hstart_ne_c hstart_ne_d
      hfinish_ne_c hfinish_ne_d).mpr hPsector⟩

/-- Trimming is compatible with canonical-closure side preservation: a walk
disjoint from the original path is disjoint from the selected crosscut. -/
theorem exists_gridCrosscut_subpath_with_side_preservation
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a b c d : GridBoundaryPosition m n}
    (p : (gridGraph m n).Walk (gridBoundaryVertex hm hn a)
      (gridBoundaryVertex hm hn b)) (hp : p.IsPath)
    (halt : CyclicallyAlternating (gridBoundaryLength_pos hm hn) a b c d)
    (q : (gridGraph m n).Walk (gridBoundaryVertex hm hn c)
      (gridBoundaryVertex hm hn d))
    (hdisjoint : ¬∃ x, x ∈ p.support ∧ x ∈ q.support) :
    ∃ P : GridCrosscut m n,
      (∀ ⦃x⦄, x ∈ P.path.support → x ∈ p.support) ∧
      CyclicallyAlternating (gridBoundaryLength_pos hm hn)
        (P.startPosition hm hn) (P.finishPosition hm hn) c d ∧
      ∀ choice,
        GridCycleSide (P.canonicalClosedWalk choice hm hn)
            (gridCollarFace (gridBoundaryVertex hm hn c)) ↔
          GridCycleSide (P.canonicalClosedWalk choice hm hn)
            (gridCollarFace (gridBoundaryVertex hm hn d)) := by
  have hcavoid : gridBoundaryVertex hm hn c ∉ p.support := by
    intro hcp
    exact hdisjoint ⟨gridBoundaryVertex hm hn c, hcp, q.start_mem_support⟩
  have hdavoid : gridBoundaryVertex hm hn d ∉ p.support := by
    intro hdp
    exact hdisjoint ⟨gridBoundaryVertex hm hn d, hdp, q.end_mem_support⟩
  obtain ⟨P, hsub, hPalt⟩ :=
    exists_gridCrosscut_subpath_preserving_alternation hm hn p hp halt
      hcavoid hdavoid
  refine ⟨P, hsub, hPalt, ?_⟩
  intro choice
  apply P.gridCycleSide_iff_of_walk_disjoint choice hm hn q
  rintro ⟨x, hxP, hxq⟩
  exact hdisjoint ⟨x, hsub hxP, hxq⟩

/-- Simple grid paths joining cyclically alternating boundary pairs share a
vertex. -/
theorem grid_paths_intersect_of_cyclicallyAlternating
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a b c d : GridBoundaryPosition m n}
    (p : (gridGraph m n).Walk (gridBoundaryVertex hm hn a)
      (gridBoundaryVertex hm hn b)) (hp : p.IsPath)
    (q : (gridGraph m n).Walk (gridBoundaryVertex hm hn c)
      (gridBoundaryVertex hm hn d))
    (halt : CyclicallyAlternating (gridBoundaryLength_pos hm hn) a b c d) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  by_contra hdisjoint
  obtain ⟨P, _, hPalt, hsame⟩ :=
    exists_gridCrosscut_subpath_with_side_preservation hm hn p hp halt q
      hdisjoint
  have hne := hPalt.pairwise_ne
  have hopposite :
      OpenCyclicSector (gridBoundaryLength_pos hm hn)
          (P.startPosition hm hn) (P.finishPosition hm hn) c ↔
        ¬OpenCyclicSector (gridBoundaryLength_pos hm hn)
          (P.startPosition hm hn) (P.finishPosition hm hn) d :=
    (cyclicallyAlternating_iff_openCyclicSector
      (gridBoundaryLength_pos hm hn) (P.startPosition hm hn)
      (P.finishPosition hm hn) c d hne.2.1.symm hne.2.2.2.1.symm
        hne.2.2.1.symm hne.2.2.2.2.1.symm).mp
      ((cyclicallyAlternating_swap_pairs (gridBoundaryLength_pos hm hn)
        _ _ _ _).mp hPalt)
  have hcside :=
    gridCycleSide_gridCollarFace_clockwise_iff_openCyclicSector P hm hn c
      hne.2.1.symm hne.2.2.2.1.symm
  have hdside :=
    gridCycleSide_gridCollarFace_clockwise_iff_openCyclicSector P hm hn d
      hne.2.2.1.symm hne.2.2.2.2.1.symm
  have hpreserved := hsame GridCollarArc.CanonicalChoice.clockwise
  tauto

end GridGraphs
