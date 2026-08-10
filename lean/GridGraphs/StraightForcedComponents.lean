import GridGraphs.Diagonal

/-!
# Local straightness of acyclic forced sets

An acyclic forced-edge graph cannot contain three corners of one unit cell in
its forced vertex set. This is the local obstruction behind the fact that a
connected full-vertex component cannot turn from horizontal to vertical.
-/

namespace GridGraphs

open SimpleGraph

/-- No three consecutive corners of a grid cell can all be forced when the
forced-edge graph is acyclic. -/
theorem grid_cell_forced_triples_free {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1))
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    ¬(cell00 r c ∈ F ∧ cell01 r c ∈ F ∧ cell11 r c ∈ F) ∧
    ¬(cell01 r c ∈ F ∧ cell11 r c ∈ F ∧ cell10 r c ∈ F) ∧
    ¬(cell11 r c ∈ F ∧ cell10 r c ∈ F ∧ cell00 r c ∈ F) ∧
    ¬(cell10 r c ∈ F ∧ cell00 r c ∈ F ∧ cell01 r c ∈ F) := by
  have hedge := grid_cell_has_unforced_edge r c hacyc
  constructor
  · rintro ⟨h00, h01, h11⟩
    rcases hedge with h | h | h | h <;> simp_all
  constructor
  · rintro ⟨h01, h11, h10⟩
    rcases hedge with h | h | h | h <;> simp_all
  constructor
  · rintro ⟨h11, h10, h00⟩
    rcases hedge with h | h | h | h <;> simp_all
  · rintro ⟨h10, h00, h01⟩
    rcases hedge with h | h | h | h <;> simp_all

private theorem forced_horizontal_vertical_turn_false {m n : Nat}
    {u v w : GridVertex m n} {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F)
    (huvRow : u.1 = v.1)
    (huvCol : u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)
    (hvwCol : v.2 = w.2)
    (hvwRow : v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val) : False := by
  rcases huvCol with huvCol | huvCol <;> rcases hvwRow with hvwRow | hvwRow
  · let r : Fin (m - 1) := ⟨v.1.val, by omega⟩
    let c : Fin (n - 1) := ⟨u.2.val, by omega⟩
    have eu : u = cell00 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c] <;> omega
    have ev : v = cell01 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, c] <;> omega
    have ew : w = cell11 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, r, c] <;> omega
    exact (grid_cell_forced_triples_free r c hacyc).1 ⟨eu ▸ hu, ev ▸ hv, ew ▸ hw⟩
  · let r : Fin (m - 1) := ⟨w.1.val, by omega⟩
    let c : Fin (n - 1) := ⟨u.2.val, by omega⟩
    have ew : w = cell01 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, c] <;> omega
    have ev : v = cell11 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, r, c] <;> omega
    have eu : u = cell10 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, r, c] <;> omega
    exact (grid_cell_forced_triples_free r c hacyc).2.1 ⟨ew ▸ hw, ev ▸ hv, eu ▸ hu⟩
  · let r : Fin (m - 1) := ⟨v.1.val, by omega⟩
    let c : Fin (n - 1) := ⟨v.2.val, by omega⟩
    have ev : v = cell00 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c] <;> omega
    have eu : u = cell01 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, c] <;> omega
    have ew : w = cell10 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, r, c] <;> omega
    exact (grid_cell_forced_triples_free r c hacyc).2.2.2 ⟨ew ▸ hw, ev ▸ hv, eu ▸ hu⟩
  · let r : Fin (m - 1) := ⟨w.1.val, by omega⟩
    let c : Fin (n - 1) := ⟨v.2.val, by omega⟩
    have ew : w = cell00 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c] <;> omega
    have eu : u = cell11 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, r, c] <;> omega
    have ev : v = cell10 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, r, c] <;> omega
    exact (grid_cell_forced_triples_free r c hacyc).2.2.1 ⟨eu ▸ hu, ev ▸ hv, ew ▸ hw⟩

/-- Two grid edges meeting at a forced vertex cannot make a perpendicular
turn. Thus three forced vertices forming a two-edge walk are all in one row or
all in one column. -/
theorem forced_two_edge_walk_parallel {m n : Nat}
    {u v w : GridVertex m n} {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F)
    (huv : (gridGraph m n).Adj u v) (hvw : (gridGraph m n).Adj v w) :
    (u.1 = v.1 ∧ v.1 = w.1) ∨ (u.2 = v.2 ∧ v.2 = w.2) := by
  change adjacent m n u v at huv
  change adjacent m n v w at hvw
  rcases huv with ⟨huvRow, huvCol⟩ | ⟨huvCol, huvRow⟩
  · rcases hvw with ⟨hvwRow, hvwCol⟩ | ⟨hvwCol, hvwRow⟩
    · exact Or.inl ⟨huvRow, hvwRow⟩
    · exact (forced_horizontal_vertical_turn_false hacyc hu hv hw
        huvRow huvCol hvwCol hvwRow).elim
  · rcases hvw with ⟨hvwRow, hvwCol⟩ | ⟨hvwCol, hvwRow⟩
    · apply (forced_horizontal_vertical_turn_false hacyc hw hv hu
        hvwRow.symm (hvwCol.elim Or.inr Or.inl) huvCol.symm
        (huvRow.elim Or.inr Or.inl)).elim
    · exact Or.inr ⟨huvCol, hvwCol⟩

/-- Reachable vertices in the grid graph induced by an acyclic forced set lie
in a common row or in a common column. In particular, this applies to every
pair of vertices in any connected component of the induced graph. -/
theorem induced_forced_reachable_same_row_or_column {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    {u v : F}
    (hreach : ((gridGraph m n).induce F).Reachable u v) :
    u.1.1 = v.1.1 ∨ u.1.2 = v.1.2 := by
  let H := (gridGraph m n).induce F
  let rec rowOfWalk {x y z : F} (hxy : H.Adj x y)
      (hrow : x.1.1 = y.1.1) (p : H.Walk y z) : y.1.1 = z.1.1 := by
    cases p with
    | nil => rfl
    | @cons _ t _ hyt p =>
        have hparallel := forced_two_edge_walk_parallel hacyc
          x.2 y.2 t.2 hxy hyt
        have hytRow : y.1.1 = t.1.1 := by
          rcases hparallel with hparallel | hparallel
          · exact hparallel.2
          · exfalso
            exact hxy.ne (Subtype.ext (Prod.ext hrow hparallel.1))
        exact hytRow.trans (rowOfWalk hyt hytRow p)
  let rec colOfWalk {x y z : F} (hxy : H.Adj x y)
      (hcol : x.1.2 = y.1.2) (p : H.Walk y z) : y.1.2 = z.1.2 := by
    cases p with
    | nil => rfl
    | @cons _ t _ hyt p =>
        have hparallel := forced_two_edge_walk_parallel hacyc
          x.2 y.2 t.2 hxy hyt
        have hytCol : y.1.2 = t.1.2 := by
          rcases hparallel with hparallel | hparallel
          · exfalso
            exact hxy.ne (Subtype.ext (Prod.ext hparallel.1 hcol))
          · exact hparallel.2
        exact hytCol.trans (colOfWalk hyt hytCol p)
  apply hreach.elim
  intro p
  cases p with
  | nil => exact Or.inl rfl
  | @cons _ w _ huw p =>
      have hadj : (gridGraph m n).Adj u.1 w.1 := huw
      change adjacent m n u.1 w.1 at hadj
      rcases hadj with ⟨hrow, _⟩ | ⟨hcol, _⟩
      · exact Or.inl (hrow.trans (rowOfWalk huw hrow p))
      · exact Or.inr (hcol.trans (colOfWalk huw hcol p))

/-- Every nonempty preconnected part of the graph induced by a forced set is
contained in one row or in one column. Taking `C` to be the support of a
connected component gives the corresponding component statement. -/
theorem induced_forced_preconnected_set_straight {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    {C : Set F} (hC : C.Nonempty)
    (hconn : ∀ ⦃u⦄, u ∈ C → ∀ ⦃v⦄, v ∈ C →
      ((gridGraph m n).induce F).Reachable u v) :
    (∃ r : Fin m, ∀ v ∈ C, v.1.1 = r) ∨
      ∃ c : Fin n, ∀ v ∈ C, v.1.2 = c := by
  classical
  obtain ⟨a, ha⟩ := hC
  by_cases hrow : ∀ v ∈ C, v.1.1 = a.1.1
  · exact Or.inl ⟨a.1.1, hrow⟩
  · push_neg at hrow
    obtain ⟨b, hb, hba⟩ := hrow
    have hab := induced_forced_reachable_same_row_or_column hacyc (hconn ha hb)
    have habCol : a.1.2 = b.1.2 := hab.resolve_left (fun h => hba h.symm)
    refine Or.inr ⟨a.1.2, ?_⟩
    intro z hz
    have haz := induced_forced_reachable_same_row_or_column hacyc (hconn ha hz)
    rcases haz with hazRow | hazCol
    · have hbz := induced_forced_reachable_same_row_or_column hacyc (hconn hb hz)
      rcases hbz with hbzRow | hbzCol
      · exact (hba (hbzRow.trans hazRow.symm)).elim
      · exact hbzCol.symm.trans habCol.symm
    · exact hazCol.symm

/-- Every connected component of the graph induced by an acyclic forced set is
contained in one row or in one column. -/
theorem induced_forced_connectedComponent_straight {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent) :
    (∃ r : Fin m, ∀ v ∈ C.supp, v.1.1 = r) ∨
      ∃ c : Fin n, ∀ v ∈ C.supp, v.1.2 = c := by
  exact induced_forced_preconnected_set_straight hacyc C.nonempty_supp
    fun _ hu _ hv => C.reachable_of_mem_supp hu hv

/-- If two vertices of an induced forced component are in the same row, every
grid vertex between them in that row belongs to the forced set and to the same
component. -/
theorem induced_forced_connectedComponent_horizontal_interval_of_le {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent)
    {u v : F} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (_hrow : u.1.1 = v.1.1) (c : Fin n)
    (huc : u.1.2.val ≤ c.val) (hcv : c.val ≤ v.1.2.val) :
    ∃ hzF : (u.1.1, c) ∈ F,
      (⟨(u.1.1, c), hzF⟩ : F) ∈ C.supp := by
  by_cases huvCol : u.1.2 = v.1.2
  · have hc : c = u.1.2 := by apply Fin.ext; omega
    subst c
    exact ⟨u.2, by simpa using hu⟩
  have hcomponentRow : ∀ w ∈ C.supp, w.1.1 = u.1.1 := by
    rcases induced_forced_connectedComponent_straight hacyc C with h | h
    · obtain ⟨r, hr⟩ := h
      intro w hw
      exact (hr w hw).trans (hr u hu).symm
    · obtain ⟨d, hd⟩ := h
      exact (huvCol ((hd u hu).trans (hd v hv).symm)).elim
  let H := (gridGraph m n).induce F
  let rec hitColumn {x y : F} (p : H.Walk x y) (hx : x ∈ C.supp)
      (hxc : x.1.2.val ≤ c.val) (hcy : c.val ≤ y.1.2.val) :
      ∃ w : F, w ∈ C.supp ∧ w.1.2 = c := by
    by_cases hxcEq : x.1.2 = c
    · exact ⟨x, hx, hxcEq⟩
    cases p with
    | nil => exact (hxcEq (Fin.ext (by omega))).elim
    | @cons _ t _ hxt p =>
        have ht : t ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hxt
        have hadj : adjacent m n x.1 t.1 := hxt
        have htc : t.1.2.val ≤ c.val := by
          rcases hadj with ⟨_, h⟩ | ⟨_, h⟩
          · rcases h with h | h <;> omega
          · omega
        exact hitColumn p ht htc hcy
  obtain ⟨w, hw, hwc⟩ := (C.reachable_of_mem_supp hu hv).elim
    fun p => hitColumn p hu huc hcv
  have hwrow := hcomponentRow w hw
  have hwval : w.1 = (u.1.1, c) := Prod.ext hwrow hwc
  have hzF : (u.1.1, c) ∈ F := by
    rw [← hwval]
    exact w.2
  refine ⟨hzF, ?_⟩
  rw [show (⟨(u.1.1, c), hzF⟩ : F) = w from Subtype.ext hwval.symm]
  exact hw

/-- The occupied columns of an induced forced component in any fixed row form
an interval. The disjunction makes the statement independent of endpoint
order. -/
theorem induced_forced_connectedComponent_horizontal_interval {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent)
    {u v : F} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hrow : u.1.1 = v.1.1) (c : Fin n)
    (hbetween :
      (u.1.2.val ≤ c.val ∧ c.val ≤ v.1.2.val) ∨
      (v.1.2.val ≤ c.val ∧ c.val ≤ u.1.2.val)) :
    ∃ hzF : (u.1.1, c) ∈ F,
      (⟨(u.1.1, c), hzF⟩ : F) ∈ C.supp := by
  rcases hbetween with hbetween | hbetween
  · exact induced_forced_connectedComponent_horizontal_interval_of_le
      hacyc C hu hv hrow c hbetween.1 hbetween.2
  · simpa only [hrow] using
      (induced_forced_connectedComponent_horizontal_interval_of_le
        hacyc C hv hu hrow.symm c hbetween.1 hbetween.2)

/-- If two vertices of an induced forced component are in the same column,
every grid vertex between them in that column belongs to the forced set and to
the same component. -/
theorem induced_forced_connectedComponent_vertical_interval_of_le {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent)
    {u v : F} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (_hcol : u.1.2 = v.1.2) (r : Fin m)
    (hur : u.1.1.val ≤ r.val) (hrv : r.val ≤ v.1.1.val) :
    ∃ hzF : (r, u.1.2) ∈ F,
      (⟨(r, u.1.2), hzF⟩ : F) ∈ C.supp := by
  by_cases huvRow : u.1.1 = v.1.1
  · have hr : r = u.1.1 := by apply Fin.ext; omega
    subst r
    exact ⟨u.2, by simpa using hu⟩
  have hcomponentCol : ∀ w ∈ C.supp, w.1.2 = u.1.2 := by
    rcases induced_forced_connectedComponent_straight hacyc C with h | h
    · obtain ⟨d, hd⟩ := h
      exact (huvRow ((hd u hu).trans (hd v hv).symm)).elim
    · obtain ⟨c, hc⟩ := h
      intro w hw
      exact (hc w hw).trans (hc u hu).symm
  let H := (gridGraph m n).induce F
  let rec hitRow {x y : F} (p : H.Walk x y) (hx : x ∈ C.supp)
      (hxr : x.1.1.val ≤ r.val) (hry : r.val ≤ y.1.1.val) :
      ∃ w : F, w ∈ C.supp ∧ w.1.1 = r := by
    by_cases hxrEq : x.1.1 = r
    · exact ⟨x, hx, hxrEq⟩
    cases p with
    | nil => exact (hxrEq (Fin.ext (by omega))).elim
    | @cons _ t _ hxt p =>
        have ht : t ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hxt
        have hadj : adjacent m n x.1 t.1 := hxt
        have htr : t.1.1.val ≤ r.val := by
          rcases hadj with ⟨_, h⟩ | ⟨_, h⟩
          · omega
          · rcases h with h | h <;> omega
        exact hitRow p ht htr hry
  obtain ⟨w, hw, hwr⟩ := (C.reachable_of_mem_supp hu hv).elim
    fun p => hitRow p hu hur hrv
  have hwcol := hcomponentCol w hw
  have hwval : w.1 = (r, u.1.2) := Prod.ext hwr hwcol
  have hzF : (r, u.1.2) ∈ F := by
    rw [← hwval]
    exact w.2
  refine ⟨hzF, ?_⟩
  rw [show (⟨(r, u.1.2), hzF⟩ : F) = w from Subtype.ext hwval.symm]
  exact hw

/-- The occupied rows of an induced forced component in any fixed column form
an interval. The disjunction makes the statement independent of endpoint
order. -/
theorem induced_forced_connectedComponent_vertical_interval {m n : Nat}
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic)
    (C : ((gridGraph m n).induce F).ConnectedComponent)
    {u v : F} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hcol : u.1.2 = v.1.2) (r : Fin m)
    (hbetween :
      (u.1.1.val ≤ r.val ∧ r.val ≤ v.1.1.val) ∨
      (v.1.1.val ≤ r.val ∧ r.val ≤ u.1.1.val)) :
    ∃ hzF : (r, u.1.2) ∈ F,
      (⟨(r, u.1.2), hzF⟩ : F) ∈ C.supp := by
  rcases hbetween with hbetween | hbetween
  · exact induced_forced_connectedComponent_vertical_interval_of_le
      hacyc C hu hv hcol r hbetween.1 hbetween.2
  · simpa only [hcol] using
      (induced_forced_connectedComponent_vertical_interval_of_le
        hacyc C hv hu hcol.symm r hbetween.1 hbetween.2)

end GridGraphs
