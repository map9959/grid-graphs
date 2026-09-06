import GridGraphs.ForcedExchange
import GridGraphs.GridCropComponents

/-!
# Ambient maximality escapes an insertable crop

If a fresh crop vertex can be added without creating a forced cycle locally,
the obstruction supplied by ambient maximality cannot be wholly retained by
the crop.
-/

namespace GridGraphs

open SimpleGraph

/-- For a maximal ambient forced forest, the obstruction to inserting the
ambient image of a locally insertable vertex has a path whose support leaves
the range of a total-three crop. -/
theorem maximalForcedAcyclic_threeSideCrop_insertable_escape
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (hmax : MaximalForcedAcyclic (gridGraph n n) F)
    (u : GridVertex (n - 3) (n - 3))
    (hu : threeSideCropEmbedding n top bottom left right hn hrows hcols u ∉ F)
    (hinsert :
      (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
        (insert u
          ((threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F))).IsAcyclic) :
    ∃ v ∈ ({threeSideCropEmbedding n top bottom left right hn hrows hcols u} ∪
          ((gridGraph n n).neighborSet
              (threeSideCropEmbedding n top bottom left right hn hrows hcols u) \ F) :
          Set (GridVertex n n)),
      ∃ w ∈ ({threeSideCropEmbedding n top bottom left right hn hrows hcols u} ∪
            ((gridGraph n n).neighborSet
                (threeSideCropEmbedding n top bottom left right hn hrows hcols u) \ F) :
            Set (GridVertex n n)),
        v ≠ w ∧
          ∃ p : (forcedEdgeGraph (gridGraph n n) F).Walk v w,
            p.IsPath ∧
              ∃ z ∈ p.support,
                z ∉ Set.range
                  (threeSideCropEmbedding n top bottom left right hn hrows hcols) := by
  classical
  let e := threeSideCropEmbedding n top bottom left right hn hrows hcols
  let localF : Set (GridVertex (n - 3) (n - 3)) := e ⁻¹' F
  have hamb := (maximalForcedAcyclic_iff_reachable.mp hmax).2 (e u) hu
  obtain ⟨v, hv, w, hw, hvw, hreach⟩ := hamb
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  refine ⟨v, hv, w, hw, hvw, p, hp, ?_⟩
  by_contra hescape
  push Not at hescape
  let P : Set (GridVertex n n) := {z | z ∈ p.support}
  let localVertex (z : P) : GridVertex (n - 3) (n - 3) :=
    Classical.choose (hescape z.1 z.2)
  have localVertex_eq (z : P) : e (localVertex z) = z.1 :=
    Classical.choose_spec (hescape z.1 z.2)
  let localMap : (forcedEdgeGraph (gridGraph n n) F).induce P →g
      forcedEdgeGraph (gridGraph (n - 3) (n - 3)) localF :=
    { toFun := fun z => localVertex z
      map_rel' := by
        intro x y hxy
        change (gridGraph (n - 3) (n - 3)).Adj (localVertex x) (localVertex y) ∧
          (localVertex x ∈ localF ∨ localVertex y ∈ localF)
        constructor
        · apply (threeSideCropEmbedding_adj_iff n top bottom left right hn hrows hcols
            (localVertex x) (localVertex y)).1
          change (gridGraph n n).Adj (e (localVertex x)) (e (localVertex y))
          rw [localVertex_eq, localVertex_eq]
          exact hxy.1
        · change e (localVertex x) ∈ F ∨ e (localVertex y) ∈ F
          rw [localVertex_eq, localVertex_eq]
          exact hxy.2 }
  let vp : P := ⟨v, p.start_mem_support⟩
  let wp : P := ⟨w, p.end_mem_support⟩
  obtain ⟨q⟩ := p.connected_induce_support vp wp
  have hlocalReach :
      (forcedEdgeGraph (gridGraph (n - 3) (n - 3)) localF).Reachable
        (localVertex vp) (localVertex wp) := (q.map localMap).reachable
  have attachment_pullback (z : P)
      (hz : z.1 ∈ ({e u} ∪ ((gridGraph n n).neighborSet (e u) \ F) :
        Set (GridVertex n n))) :
      localVertex z ∈ ({u} ∪
        ((gridGraph (n - 3) (n - 3)).neighborSet u \ localF) :
          Set (GridVertex (n - 3) (n - 3))) := by
    rcases hz with hz | hz
    · left
      apply e.injective
      rw [localVertex_eq]
      exact hz
    · right
      constructor
      · apply (threeSideCropEmbedding_adj_iff n top bottom left right hn hrows hcols
          u (localVertex z)).1
        rw [localVertex_eq]
        exact hz.1
      · change e (localVertex z) ∉ F
        rw [localVertex_eq]
        exact hz.2
  have hvLocal := attachment_pullback vp hv
  have hwLocal := attachment_pullback wp hw
  have hvwLocal : localVertex vp ≠ localVertex wp := by
    intro h
    apply hvw
    have hvEq : e (localVertex vp) = v := by
      simpa [vp] using localVertex_eq vp
    have hwEq : e (localVertex wp) = w := by
      simpa [wp] using localVertex_eq wp
    exact hvEq.symm.trans ((congrArg e h).trans hwEq)
  have hlocalAcyclic :
      (forcedEdgeGraph (gridGraph (n - 3) (n - 3)) localF).IsAcyclic := by
    exact forcedEdgeGraph_threeSideCrop_isAcyclic
      n top bottom left right hn hrows hcols F hmax.1
  have huLocal : u ∉ localF := hu
  have hnoReach := (forcedEdgeGraph_insert_isAcyclic_iff huLocal hlocalAcyclic).mp hinsert
  exact hnoReach hvLocal hwLocal hvwLocal hlocalReach

/-- An ambient grid vertex outside a rectangular crop cannot be adjacent to
two distinct vertices of the crop. -/
private theorem outside_gridOffsetEmbedding_adjacent_unique
    {p q m n rowOffset colOffset : Nat}
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    {z x y : GridVertex m n}
    (hz : z ∉ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols))
    (hx : x ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols))
    (hy : y ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols))
    (hzx : (gridGraph m n).Adj z x) (hzy : (gridGraph m n).Adj z y) :
    x = y := by
  rw [mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols] at hx hy
  rw [mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols] at hz
  change adjacent m n z x at hzx
  change adjacent m n z y at hzy
  unfold adjacent at hzx hzy
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- If a simple forced-edge path has retained endpoints but leaves a
rectangular crop, then one of its outside vertices is forced.  Otherwise an
outside vertex of the path would have two distinct retained path-neighbors,
which rectangular geometry forbids. -/
theorem forcedEdgePath_exists_forced_outside_gridOffsetEmbedding
    {p q m n rowOffset colOffset : Nat}
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (F : Set (GridVertex m n)) {v w : GridVertex m n}
    (P : (forcedEdgeGraph (gridGraph m n) F).Walk v w)
    (hP : P.IsPath)
    (hv : v ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols))
    (hw : w ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols))
    (hescape : ∃ z ∈ P.support,
      z ∉ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols)) :
    ∃ z ∈ P.support, z ∈ F ∧
      z ∉ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) := by
  classical
  by_contra hforced
  push Not at hforced
  obtain ⟨z, hzP, hzout⟩ := hescape
  obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzP
  have hi0 : i ≠ 0 := by
    intro hi0
    apply hzout
    rw [← hiz, hi0, P.getVert_zero]
    exact hv
  have hilength : i < P.length := by
    by_contra hlt
    have hieq : i = P.length := by omega
    apply hzout
    rw [← hiz, hieq, P.getVert_length]
    exact hw
  have hprev := P.adj_getVert_succ (show i - 1 < P.length by omega)
  have hnext := P.adj_getVert_succ hilength
  have hznotF : P.getVert i ∉ F := by
    intro hzF
    apply hzout
    rw [← hiz]
    exact hforced (P.getVert i) (P.getVert_mem_support i) hzF
  have hprevF : P.getVert (i - 1) ∈ F := by
    rcases hprev.2 with h | h
    · exact h
    · exact (hznotF (by simpa [show i - 1 + 1 = i by omega] using h)).elim
  have hnextF : P.getVert (i + 1) ∈ F := by
    exact hnext.2.resolve_left hznotF
  have hprevIn : P.getVert (i - 1) ∈
      Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) :=
    hforced _ (P.getVert_mem_support _) hprevF
  have hnextIn : P.getVert (i + 1) ∈
      Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) :=
    hforced _ (P.getVert_mem_support _) hnextF
  have hneighbors : P.getVert (i - 1) = P.getVert (i + 1) := by
    apply outside_gridOffsetEmbedding_adjacent_unique hrows hcols hzout hprevIn hnextIn
    · simpa [hiz, show i - 1 + 1 = i by omega] using hprev.1.symm
    · simpa [hiz] using hnext.1
  have hindices : i - 1 = i + 1 := hP.getVert_injOn
    (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hneighbors
  omega

/-- Every ambient neighbor of an interior vertex of an offset crop is still
inside the crop. -/
private theorem gridOffsetEmbedding_neighbor_mem_range_of_interior
    {p q m n rowOffset colOffset : Nat}
    (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
    (u : GridVertex p q)
    (hrowStart : 0 < u.1.val) (hrowEnd : u.1.val + 1 < p)
    (hcolStart : 0 < u.2.val) (hcolEnd : u.2.val + 1 < q)
    {z : GridVertex m n}
    (hz : (gridGraph m n).Adj
      (gridOffsetEmbedding rowOffset colOffset hrows hcols u) z) :
    z ∈ Set.range (gridOffsetEmbedding rowOffset colOffset hrows hcols) := by
  rw [mem_range_gridOffsetEmbedding_iff rowOffset colOffset hrows hcols]
  change adjacent m n (gridOffsetEmbedding rowOffset colOffset hrows hcols u) z at hz
  unfold adjacent at hz
  rcases hz with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · have hrowVal := congrArg Fin.val hrow
    simp only [gridOffsetEmbedding_fst_val] at hrowVal
    rcases hcol with hcol | hcol
    · change colOffset + u.2.val + 1 = z.2.val at hcol
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    · change z.2.val + 1 = colOffset + u.2.val at hcol
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
  · have hcolVal := congrArg Fin.val hcol
    simp only [gridOffsetEmbedding_snd_val] at hcolVal
    rcases hrow with hrow | hrow
    · change rowOffset + u.1.val + 1 = z.1.val at hrow
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    · change z.1.val + 1 = rowOffset + u.1.val at hrow
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega

/-- For an insertable vertex in the strict interior of a total-three crop,
the escaping path supplied by ambient maximality contains a forced vertex
outside the crop.  The four coordinate hypotheses are needed: without them an
outside unforced attachment can be a path endpoint and immediately return to
an inside forced vertex. -/
theorem maximalForcedAcyclic_threeSideCrop_insertable_forced_escape
    (n top bottom left right : Nat) (hn : 3 ≤ n)
    (hrows : top + bottom = 3) (hcols : left + right = 3)
    (F : Set (GridVertex n n))
    (hmax : MaximalForcedAcyclic (gridGraph n n) F)
    (u : GridVertex (n - 3) (n - 3))
    (hrowStart : 0 < u.1.val) (hrowEnd : u.1.val + 1 < n - 3)
    (hcolStart : 0 < u.2.val) (hcolEnd : u.2.val + 1 < n - 3)
    (hu : threeSideCropEmbedding n top bottom left right hn hrows hcols u ∉ F)
    (hinsert :
      (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
        (insert u
          ((threeSideCropEmbedding n top bottom left right hn hrows hcols) ⁻¹' F))).IsAcyclic) :
    ∃ v ∈ ({threeSideCropEmbedding n top bottom left right hn hrows hcols u} ∪
          ((gridGraph n n).neighborSet
              (threeSideCropEmbedding n top bottom left right hn hrows hcols u) \ F) :
          Set (GridVertex n n)),
      ∃ w ∈ ({threeSideCropEmbedding n top bottom left right hn hrows hcols u} ∪
            ((gridGraph n n).neighborSet
                (threeSideCropEmbedding n top bottom left right hn hrows hcols u) \ F) :
            Set (GridVertex n n)),
        v ≠ w ∧
          ∃ P : (forcedEdgeGraph (gridGraph n n) F).Walk v w,
            P.IsPath ∧
              ∃ z ∈ P.support, z ∈ F ∧
                z ∉ Set.range
                  (threeSideCropEmbedding n top bottom left right hn hrows hcols) := by
  classical
  let e := threeSideCropEmbedding n top bottom left right hn hrows hcols
  obtain ⟨v, hv, w, hw, hvw, P, hP, hescape⟩ :=
    maximalForcedAcyclic_threeSideCrop_insertable_escape
      n top bottom left right hn hrows hcols F hmax u hu hinsert
  have attachment_mem_range {x : GridVertex n n}
      (hx : x ∈ ({e u} ∪ ((gridGraph n n).neighborSet (e u) \ F) :
        Set (GridVertex n n))) : x ∈ Set.range e := by
    rcases hx with rfl | hx
    · exact ⟨u, rfl⟩
    · exact gridOffsetEmbedding_neighbor_mem_range_of_interior
        (rowOffset := top) (colOffset := left) (by omega) (by omega) u
        hrowStart hrowEnd hcolStart hcolEnd hx.1
  refine ⟨v, hv, w, hw, hvw, P, hP, ?_⟩
  exact forcedEdgePath_exists_forced_outside_gridOffsetEmbedding
    (rowOffset := top) (colOffset := left) (by omega) (by omega) F P hP
    (attachment_mem_range hv) (attachment_mem_range hw) hescape

end GridGraphs
