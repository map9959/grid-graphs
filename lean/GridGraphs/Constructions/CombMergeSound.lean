import GridGraphs.Constructions.CombWord

namespace GridGraphs.CombWord
open SimpleGraph

/-- A global extension of the labels on the current ports. Labels may
overestimate connectivity: unequal labels still certify separation,
including paths through vertices no longer present on the frontier. -/
def ExtendsLabels {V : Type*} (G : SimpleGraph V) (port : Nat → V) (p : List Nat) : Prop :=
  ∃ c : V → Nat, (∀ ⦃x y⦄, G.Adj x y → c x = c y) ∧
    ∀ (i a : Nat), p[i]? = some a → c (port i) = a

private theorem walk_color {V : Type*} {G : SimpleGraph V} {c : V → Nat}
    (hc : ∀ ⦃x y⦄, G.Adj x y → c x = c y) {u v : V} (w : G.Walk u v) :
    c u = c v := by
  induction w with
  | nil => rfl
  | cons e _ ih => exact (hc e).trans ih

def insertPort {V : Type*} (port : Nat → V) (G : SimpleGraph V) (e : Nat × Nat) :=
  G ⊔ edge (port e.1) (port e.2)

/-- The actual `merge` program cannot accept an edge closing a graph cycle.
Moreover its returned list is valid for all remaining graph insertions. -/
theorem merge_sound {V : Type*} {G : SimpleGraph V} {port : Nat → V}
    {p q : List Nat} {e : Nat × Nat} (hf : G.IsAcyclic)
    (hp : ExtendsLabels G port p) (h : merge p e = some q) :
    (insertPort port G e).IsAcyclic ∧ ExtendsLabels (insertPort port G e) port q := by
  obtain ⟨c,hc,hp⟩ := hp
  cases ha : p[e.1]? with
  | none => simp [merge,ha] at h
  | some a =>
    cases hb : p[e.2]? with
    | none => simp [merge,ha,hb] at h
    | some b =>
      by_cases hab : a = b
      · simp [merge,ha,hb,hab] at h
      simp [merge,ha,hb,hab] at h
      subst q
      have ca := hp _ _ ha
      have cb := hp _ _ hb
      refine ⟨hf.sup_edge_of_not_reachable (fun ⟨w⟩ => hab
        (ca.symm.trans ((walk_color hc w).trans cb))), ?_⟩
      let f := fun t : Nat => if t = a then b else t
      refine ⟨fun x => f (c x), ?_, ?_⟩
      · intro x y hxy
        rcases hxy with hxy | hxy
        · exact congrArg f (hc hxy)
        · have huv := ((edge_adj _ _ _ _).mp hxy).1
          rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [f,ca,cb]
      · intro i d hd
        rw [List.getElem?_map] at hd
        cases hs : p[i]? with
        | none => simp [hs] at hd
        | some z =>
          simp [hs] at hd
          simpa [f,hp _ _ hs] using hd

/-- Soundness for an entire column's ordered edge list, including edges
whose endpoint components have already changed within that column. -/
theorem fold_merge_sound {V : Type*} (port : Nat → V) (es : List (Nat × Nat))
    {G : SimpleGraph V} {p q : List Nat} (hf : G.IsAcyclic)
    (hp : ExtendsLabels G port p) (h : es.foldlM merge p = some q) :
    (es.foldl (insertPort port) G).IsAcyclic ∧
      ExtendsLabels (es.foldl (insertPort port) G) port q := by
  induction es generalizing G p with
  | nil =>
    simp at h
    subst q
    exact ⟨hf,hp⟩
  | cons e es ih =>
    cases hs : merge p e with
    | none => simp [List.foldlM_cons,hs] at h
    | some p' =>
      have h' := merge_sound hf hp hs
      exact ih h'.1 h'.2 (by simpa [List.foldlM_cons,hs] using h)

end GridGraphs.CombWord
