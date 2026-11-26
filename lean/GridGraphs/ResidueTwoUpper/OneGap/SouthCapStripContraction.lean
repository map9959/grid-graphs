import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripRimWire

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

/-- Two edge-disjoint parts of a forest cannot both connect the same
distinct pair. No disjointness of the vertex sets is required; in
particular the interior and exterior may share their contacts. -/
theorem not_reachable_of_external {V : Type} {G I E : SimpleGraph V}
    (acy : G.IsAcyclic) (interior : I≤G) (exterior : E≤G)
    (disj : Disjoint I.edgeSet E.edgeSet) {x y : V} (neq : x≠y)
    (wire : E.Reachable x y) : ¬I.Reachable x y := by
  intro internal
  apply (isAcyclic_iff_pairwise_not_isEdgeReachable_two.mp acy) neq
  rw [isEdgeReachable_two]
  intro e
  have avoid {A : SimpleGraph V} (sub : A≤G) (absent : e∉A.edgeSet) :
      A≤G.deleteEdges {e} := by
    intro a b ab
    simp only [deleteEdges_adj,Set.mem_singleton_iff]
    exact ⟨sub ab,fun eq => absent (eq ▸ ((mem_edgeSet A).mpr ab))⟩
  by_cases hit : e∈I.edgeSet
  · exact wire.mono (avoid exterior (fun other => Set.disjoint_left.mp disj hit other))
  · exact internal.mono (avoid interior hit)

/-- Keep all interior edges and attach a fresh root to each selected
vertex. This is the graph whose connections the strip engine sweeps. -/
def apexGraph {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) :
    SimpleGraph (Option V) where
  Adj x y := match x,y with
    | some a,some b => G.Adj a b
    | some a,none => a∈C
    | none,some b => b∈C
    | none,none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> first | exact fun h => G.adj_symm h | exact id⟩
  loopless := ⟨by intro x; cases x <;> first | exact fun e => G.loopless.irrefl _ e | exact id⟩

private theorem path_to_apex_aux {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V)
    {a z : Option V} (w : (apexGraph G C).Walk a z) :
    ∀ x, a=some x → z=none → ∃ c∈C, G.Reachable x c := by
  induction w with
  | nil => intro x a b; cases a.symm.trans b
  | @cons a b z edge w ih =>
    intro x atX atZ
    subst a
    cases b with
    | none => exact ⟨x,edge,.rfl⟩
    | some y =>
      obtain ⟨c,hc,reach⟩ := ih y rfl atZ
      have e : G.Adj x y := edge
      exact ⟨c,hc,e.reachable.trans reach⟩

theorem path_to_apex {V : Type} [DecidableEq V] {G : SimpleGraph V} {C : Finset V} {x : V}
    (r : (apexGraph G C).Reachable (some x) none) : ∃ c∈C, G.Reachable x c :=
  let ⟨w⟩ := r
  path_to_apex_aux G C w x rfl rfl

private theorem apex_empty_acyclic {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (acy : G.IsAcyclic) : (apexGraph G ∅).IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro x y e
  cases x with
  | none => cases y <;> simp [apexGraph] at e
  | some a =>
    cases y with
    | none => simp [apexGraph] at e
    | some b =>
      apply isBridge_iff.mpr
      intro reach
      let f : ((apexGraph G ∅).deleteEdges {s(some a,some b)}) →g G.deleteEdges {s(a,b)} :=
        ⟨fun v => v.getD a,by
          intro u v uv
          simp only [deleteEdges_adj,Set.mem_singleton_iff] at uv ⊢
          cases u <;> cases v <;> simp only [apexGraph,Finset.notMem_empty] at uv <;>
            first | exact False.elim uv.1
                  | exact ⟨uv.1,fun h => uv.2 (congrArg (Sym2.map some) h)⟩⟩
      exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp acy e)) (reach.map f)

private theorem apex_insert {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) (x : V) :
    apexGraph G (insert x C) = apexGraph G C ⊔ SimpleGraph.edge (some x) none := by
  ext a b
  cases a <;> cases b <;> simp [apexGraph,edge_adj] <;> tauto

/-- Wiring any number of separate forest components to one fresh
apex is acyclic. Each addition joins previously unreachable vertices. -/
theorem apex_acyclic {V : Type} [DecidableEq V] {G : SimpleGraph V} (acy : G.IsAcyclic)
    (C : Finset V) (separate : ∀ x∈C, ∀ y∈C, x≠y → ¬G.Reachable x y) :
    (apexGraph G C).IsAcyclic := by
  induction C using Finset.induction_on with
  | empty => exact apex_empty_acyclic acy
  | @insert x C fresh ih =>
    rw [apex_insert]
    have acy' := ih (fun a ha b hb => separate a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
    apply acy'.sup_edge_of_not_reachable
    intro reach
    obtain ⟨y,hy,hxy⟩ := path_to_apex reach
    have ne : x≠y := fun eq => fresh (eq.symm ▸ hy)
    exact separate x (Finset.mem_insert_self ..) y (Finset.mem_insert_of_mem hy) ne hxy

/-- Reusable common-root contraction criterion. Its exterior can be a
physical perimeter and a north branch, provided they use no retained
interior edge. No arbitrary identification of open sites is justified. -/
theorem apex_acyclic_of_exterior {V : Type} [DecidableEq V] {G I E : SimpleGraph V}
    (acy : G.IsAcyclic) (interior : I≤G) (exterior : E≤G)
    (disj : Disjoint I.edgeSet E.edgeSet) (C : Finset V)
    (connected : ∀ x∈C, ∀ y∈C, E.Reachable x y) :
    (apexGraph I C).IsAcyclic :=
  apex_acyclic (acy.anti interior) C fun x hx y hy ne =>
    not_reachable_of_external acy interior exterior disj ne (connected x hx y hy)

/-- Retraction across pendant branches: an interior excursion may
collapse to a point, but cannot alter connectivity of fixed contacts. -/
theorem reachable_retract {V : Type} {I J : SimpleGraph V} (f : V → V)
    (edges : ∀ a b, I.Adj a b → f a=f b ∨ J.Adj (f a) (f b))
    {x y : V} (r : I.Reachable x y) : J.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := r
  induction p with
  | nil => exact .rfl
  | @cons a b c e p ih =>
    rcases edges a b e with h|h
    · exact h ▸ ih
    · exact h.reachable.trans ih

/-- Shared pendant edges may remain in the engine's interior graph.
Only its retracted core must be disjoint from the physical exterior
paths. The contraction leaves all original interior vertices intact. -/
theorem apex_acyclic_of_retracted_exterior {V : Type} [DecidableEq V]
    {G I J E : SimpleGraph V} (acy : G.IsAcyclic) (interior : I≤G) (core : J≤G)
    (exterior : E≤G) (disj : Disjoint J.edgeSet E.edgeSet)
    (C : Finset V) (f : V → V) (fixed : ∀ x∈C, f x=x)
    (edges : ∀ a b, I.Adj a b → f a=f b ∨ J.Adj (f a) (f b))
    (connected : ∀ x∈C, ∀ y∈C, E.Reachable x y) :
    (apexGraph I C).IsAcyclic := by
  apply apex_acyclic (acy.anti interior)
  intro x hx y hy ne r
  have rr := reachable_retract f edges r
  rw [fixed x hx,fixed y hy] at rr
  exact not_reachable_of_external acy core exterior disj ne (connected x hx y hy) rr

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
