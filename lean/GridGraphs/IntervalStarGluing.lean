import GridGraphs.Forced

/-!
# Gluing forests at most one active vertex

The union of two forests is a forest when the sets of their non-isolated
vertices have at most one vertex in common.  No finiteness assumptions are
needed.
-/

namespace SimpleGraph

variable {V : Type*} {G H K : SimpleGraph V}

private theorem Walk.edges_left_or_exists_right {u v : V}
    (p : K.Walk u v) (hK : K ≤ G ⊔ H) :
    (∀ e, e ∈ p.edges → e ∈ G.edgeSet) ∨
      ∃ e, e ∈ p.edges ∧ e ∈ H.edgeSet := by
  induction p with
  | nil =>
      exact Or.inl (by simp)
  | @cons u v w h p ih =>
      rcases (sup_adj G H u v).mp (hK h) with hg | hh
      · rcases ih with hall | ⟨e, he, heH⟩
        · exact Or.inl (by
            intro e he
            simp only [Walk.edges_cons, List.mem_cons] at he
            rcases he with rfl | he
            · exact hg
            · exact hall e he)
        · exact Or.inr ⟨e, by simp [he], heH⟩
      · exact Or.inr ⟨s(u, v), by simp, hh⟩

private theorem Walk.exists_common_on_crossing {u v : V}
    (p : K.Walk u v) (hK : K ≤ G ⊔ H)
    (hu : u ∈ H.support) (hv : v ∈ G.support) :
    ∃ x, x ∈ p.support ∧ x ∈ G.support ∩ H.support := by
  induction p with
  | nil =>
      simpa using And.intro hv hu
  | @cons u v w h p ih =>
      rcases (sup_adj G H u v).mp (hK h) with hg | hh
      · exact ⟨u, Walk.start_mem_support _, ⟨⟨v, hg⟩, hu⟩⟩
      · obtain ⟨x, hxp, hx⟩ := ih ⟨u, hh.symm⟩ hv
        exact ⟨x, by simp [hxp], hx⟩

private theorem Walk.exists_two_common_of_right_edge {u v : V}
    (p : K.Walk u v) (hK : K ≤ G ⊔ H) (hp : p.IsPath)
    (hu : u ∈ G.support) (hv : v ∈ G.support)
    (hright : ∃ e, e ∈ p.edges ∧ e ∈ H.edgeSet) :
    ∃ x ∈ G.support ∩ H.support, ∃ y ∈ G.support ∩ H.support, x ≠ y := by
  induction p with
  | nil => simp at hright
  | @cons u v w h p ih =>
      have hp' := (Walk.cons_isPath_iff h p).mp hp
      rcases (sup_adj G H u v).mp (hK h) with hg | hh
      · obtain ⟨e, he, heH⟩ := hright
        simp only [Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he
        · exact ⟨u, ⟨hu, ⟨v, heH⟩⟩, v,
            ⟨⟨u, hg.symm⟩, ⟨u, heH.symm⟩⟩,
              fun huv => G.loopless.irrefl u (huv ▸ hg)⟩
        · exact ih hp'.1 ⟨u, hg.symm⟩ hv ⟨e, he, heH⟩
      · obtain ⟨y, hyp, hy⟩ :=
          p.exists_common_on_crossing hK ⟨u, hh.symm⟩ hv
        exact ⟨u, ⟨hu, ⟨v, hh⟩⟩, y, hy, fun huy => hp'.2 (huy ▸ hyp)⟩

/-- The supremum of two forests is a forest if their active supports meet in
at most one vertex. -/
theorem IsAcyclic.sup_of_support_inter_subsingleton
    (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (hinter : (G.support ∩ H.support).Subsingleton) :
    (G ⊔ H).IsAcyclic := by
  intro u c hc
  cases c with
  | nil => exact Walk.not_isCycle_nil hc
  | cons h p =>
      have hp : p.IsPath := ((Walk.cons_isCycle_iff p h).mp hc).1
      rcases (sup_adj G H _ _).mp h with hg | hh
      · rcases p.edges_left_or_exists_right (G := G) (H := H) le_rfl with hall | hright
        · let cG := (Walk.cons h p).transfer G (by
            intro e he
            simp only [Walk.edges_cons, List.mem_cons] at he
            rcases he with rfl | he
            · exact hg
            · exact hall e he)
          exact hG cG (hc.transfer _)
        · obtain ⟨x, hx, y, hy, hxy⟩ :=
            p.exists_two_common_of_right_edge le_rfl hp
              ⟨_, hg.symm⟩ ⟨_, hg⟩ hright
          exact hxy (hinter hx hy)
      · have hswap : G ⊔ H ≤ H ⊔ G := by
          intro x y hxy
          rcases (sup_adj G H x y).mp hxy with hGxy | hHxy
          · exact (sup_adj H G x y).mpr (Or.inr hGxy)
          · exact (sup_adj H G x y).mpr (Or.inl hHxy)
        rcases p.edges_left_or_exists_right (G := H) (H := G) hswap with hall | hleft
        · let cH := (Walk.cons h p).transfer H (by
            intro e he
            simp only [Walk.edges_cons, List.mem_cons] at he
            rcases he with rfl | he
            · exact hh
            · exact hall e he)
          exact hH cH (hc.transfer _)
        · obtain ⟨x, hx, y, hy, hxy⟩ :=
            p.exists_two_common_of_right_edge (G := H) (H := G) hswap hp
              ⟨_, hh.symm⟩ ⟨_, hh⟩ hleft
          exact hxy (hinter ⟨hx.2, hx.1⟩ ⟨hy.2, hy.1⟩)

/-- The union of a list of simple graphs. -/
def listUnion : List (SimpleGraph V) → SimpleGraph V
  | [] => ⊥
  | G :: graphs => G ⊔ listUnion graphs

@[simp] theorem listUnion_nil : listUnion ([] : List (SimpleGraph V)) = ⊥ :=
  rfl

@[simp] theorem listUnion_cons (G : SimpleGraph V) (graphs : List (SimpleGraph V)) :
    listUnion (G :: graphs) = G ⊔ listUnion graphs :=
  rfl

@[simp] theorem support_sup (G H : SimpleGraph V) :
    (G ⊔ H).support = G.support ∪ H.support := by
  ext v
  simp only [mem_support, sup_adj, Set.mem_union]
  constructor
  · rintro ⟨w, hG | hH⟩
    · exact Or.inl ⟨w, hG⟩
    · exact Or.inr ⟨w, hH⟩
  · rintro (⟨w, hG⟩ | ⟨w, hH⟩)
    · exact ⟨w, Or.inl hG⟩
    · exact ⟨w, Or.inr hH⟩

@[simp] theorem support_listUnion_nil :
    (listUnion ([] : List (SimpleGraph V))).support = ∅ := by
  simp

@[simp] theorem support_listUnion_cons (G : SimpleGraph V)
    (graphs : List (SimpleGraph V)) :
    (listUnion (G :: graphs)).support = G.support ∪ (listUnion graphs).support := by
  simp

/-- A leaf-elimination certificate for a list of forests. At each step, the
active support of the head meets the union of the remaining pieces in at most
one vertex. -/
inductive ListGluingCertificate : List (SimpleGraph V) → Prop
  | nil : ListGluingCertificate []
  | cons {G : SimpleGraph V} {graphs : List (SimpleGraph V)}
      (head_acyclic : G.IsAcyclic)
      (tail : ListGluingCertificate graphs)
      (support_inter : (G.support ∩ (listUnion graphs).support).Subsingleton) :
      ListGluingCertificate (G :: graphs)

namespace ListGluingCertificate

/-- A certified leaf-elimination order has acyclic total union. -/
theorem isAcyclic {graphs : List (SimpleGraph V)}
    (certificate : ListGluingCertificate graphs) : (listUnion graphs).IsAcyclic := by
  induction certificate with
  | nil => simp
  | cons head_acyclic _ support_inter tail_acyclic =>
      exact head_acyclic.sup_of_support_inter_subsingleton tail_acyclic support_inter

end ListGluingCertificate

/-- A list union selected from a function-indexed family of pieces. -/
def indexedListUnion {I : Type*} (pieces : I → SimpleGraph V) (order : List I) :
    SimpleGraph V :=
  listUnion (order.map pieces)

/-- A leaf-elimination certificate for a function-indexed list of pieces. -/
abbrev IndexedListGluingCertificate {I : Type*} (pieces : I → SimpleGraph V)
    (order : List I) : Prop :=
  ListGluingCertificate (order.map pieces)

/-- An indexed list union is acyclic when its order has a gluing certificate. -/
theorem IndexedListGluingCertificate.isAcyclic {I : Type*}
    {pieces : I → SimpleGraph V} {order : List I}
    (certificate : IndexedListGluingCertificate pieces order) :
    (indexedListUnion pieces order).IsAcyclic :=
  ListGluingCertificate.isAcyclic certificate

end SimpleGraph

namespace GridGraphs

open SimpleGraph

/-- Union of the center sets listed by an interval-star elimination order. -/
def indexedListSetUnion {I V : Type*} (centers : I → Set V) : List I → Set V
  | [] => ∅
  | i :: order => centers i ∪ indexedListSetUnion centers order

@[simp] theorem indexedListSetUnion_nil {I V : Type*} (centers : I → Set V) :
    indexedListSetUnion centers [] = ∅ := rfl

@[simp] theorem indexedListSetUnion_cons {I V : Type*} (centers : I → Set V)
    (i : I) (order : List I) :
    indexedListSetUnion centers (i :: order) =
      centers i ∪ indexedListSetUnion centers order := rfl

/-- Forcing a union of center sets is the union of their forced stars. -/
theorem forcedEdgeGraph_union {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    forcedEdgeGraph G (A ∪ B) =
      forcedEdgeGraph G A ⊔ forcedEdgeGraph G B := by
  ext v w
  simp only [forcedEdgeGraph, SimpleGraph.sup_adj, Set.mem_union]
  tauto

/-- The forced graph of all listed centers is exactly the indexed union of the
individual interval-star pieces. -/
theorem indexedListUnion_forcedEdgeGraph {I V : Type*}
    (G : SimpleGraph V) (centers : I → Set V) (order : List I) :
    SimpleGraph.indexedListUnion
        (fun i => forcedEdgeGraph G (centers i)) order =
      forcedEdgeGraph G (indexedListSetUnion centers order) := by
  induction order with
  | nil =>
      ext v w
      simp [SimpleGraph.indexedListUnion,
        indexedListSetUnion, forcedEdgeGraph]
  | cons i order ih =>
      simp only [SimpleGraph.indexedListUnion, List.map_cons,
        SimpleGraph.listUnion_cons, indexedListSetUnion_cons]
      change forcedEdgeGraph G (centers i) ⊔
          SimpleGraph.indexedListUnion
            (fun j => forcedEdgeGraph G (centers j)) order = _
      rw [ih, forcedEdgeGraph_union]

/-- A leaf-elimination certificate for interval-star pieces proves acyclicity
of the forced graph of their complete center union. -/
theorem forcedEdgeGraph_indexedListSetUnion_isAcyclic {I V : Type*}
    (G : SimpleGraph V) (centers : I → Set V) (order : List I)
    (certificate : SimpleGraph.IndexedListGluingCertificate
      (fun i => forcedEdgeGraph G (centers i)) order) :
    (forcedEdgeGraph G (indexedListSetUnion centers order)).IsAcyclic := by
  rw [← indexedListUnion_forcedEdgeGraph G centers order]
  exact certificate.isAcyclic

/-- Construction-facing form of a tree-shaped interval-star incidence graph.
The list is a leaf-elimination order: every listed star is a forest, and when
it is eliminated it has at most one physical attachment vertex in the suffix. -/
structure IntervalStarGluingOrder {I V : Type*} (G : SimpleGraph V)
    (centers : I → Set V) (order : List I) : Prop where
  piece_acyclic : ∀ i, i ∈ order → (forcedEdgeGraph G (centers i)).IsAcyclic
  unique_attachment : ∀ (before : List I) (i : I) (suffix : List I),
    order = before ++ i :: suffix →
      ((forcedEdgeGraph G (centers i)).support ∩
        (SimpleGraph.indexedListUnion
          (fun j => forcedEdgeGraph G (centers j)) suffix).support).Subsingleton

namespace IntervalStarGluingOrder

theorem toCertificate {I V : Type*} {G : SimpleGraph V}
    {centers : I → Set V} {order : List I}
    (data : IntervalStarGluingOrder G centers order) :
    SimpleGraph.IndexedListGluingCertificate
      (fun i => forcedEdgeGraph G (centers i)) order := by
  induction order with
  | nil => exact .nil
  | cons i order ih =>
      apply SimpleGraph.ListGluingCertificate.cons
      · exact data.piece_acyclic i (by simp)
      · apply ih
        refine {
          piece_acyclic := ?_
          unique_attachment := ?_
        }
        · intro j hj
          exact data.piece_acyclic j (by simp [hj])
        · intro before j suffix hsplit
          apply data.unique_attachment (i :: before) j suffix
          simp only [List.cons_append]
          rw [hsplit]
      · simpa [SimpleGraph.indexedListUnion] using
          data.unique_attachment [] i order rfl

/-- The forced union of a tree-shaped interval-star family is a forest. -/
theorem forcedEdgeGraph_isAcyclic {I V : Type*} {G : SimpleGraph V}
    {centers : I → Set V} {order : List I}
    (data : IntervalStarGluingOrder G centers order) :
    (forcedEdgeGraph G (indexedListSetUnion centers order)).IsAcyclic :=
  forcedEdgeGraph_indexedListSetUnion_isAcyclic G centers order data.toCertificate

end IntervalStarGluingOrder

end GridGraphs
