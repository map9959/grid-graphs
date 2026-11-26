import GridGraphs.NoPitch.FaceJoinLabels

namespace GridGraphs.NoPitch.FaceJoin
open Finset SimpleGraph PitchCut
variable {k : Nat} (F : Finset (Site k))

/-- A newly forced edge touches an interior mark. Such a vertex belongs
to only one closed face, even when the other endpoint lies on a seam. -/
theorem new_edge_unique {x y : Site k} (e : (Budget.G F).Adj x y)
    (new : ¬(Budget.base F).Adj x y) {p q : FacePos k}
    (px : box p x) (py : box p y) (qx : box q x) (qy : box q y) : p=q := by
  have unique (z : Site k) (pz : box p z) (qz : box q z)
      (m : z∈F) (no : z∉skeleton F) : p=q := by
    have r : ¬(z.1.val%3=0 ∨ z.2.val%3=0) := fun h => no (mem_filter.mpr ⟨m,h⟩)
    unfold box at pz qz
    apply Prod.ext <;> apply Fin.ext <;> omega
  rcases e.2 with h|h
  · exact unique x px qx h (fun old => new ⟨e.1,.inl old⟩)
  · exact unique y py qy h (fun old => new ⟨e.1,.inr old⟩)

theorem charges_disjoint {p q : FacePos k} (ne : p≠q) : Disjoint (charges F p) (charges F q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hp hq
  obtain ⟨ex,px,py⟩ := mem_filter.mp hp
  obtain ⟨_,qx,qy⟩ := mem_filter.mp hq
  obtain ⟨_,nx,missing⟩ := mem_filter.mp ex
  have step := (CapBill.parent_step _ (Budget.sectionRoot F)
    (mt (CapBill.parent_fix _ _ x).mpr nx)).1
  exact ne (new_edge_unique F step missing px py qx qy)

noncomputable def total := ∑ p : FacePos k, joins (faceMask F p) (faceAtom F p).2

/-- Uniform physical `R ≤ E`, with no no-pitch or maximizer assumption.
The edge assigned to a charge is the full-forest parent edge, not a local
choice of orientation. -/
theorem total_le_exits (acy : (Budget.G F).IsAcyclic) :
    total F ≤ (Budget.exits F).card := by
  classical
  have dis : (↑(univ : Finset (FacePos k)) : Set _).PairwiseDisjoint (charges F) :=
    fun _ _ _ _ ne => charges_disjoint F ne
  have sub : univ.biUnion (charges F) ⊆ Budget.exits F := by
    intro x hx; obtain ⟨p,_,hp⟩ := mem_biUnion.mp hx; exact (mem_filter.mp hp).1
  calc
    _ ≤ ∑ p, (charges F p).card := sum_le_sum fun p _ => joins_le_charges F p acy
    _ = _ := (card_biUnion (s:=univ) dis).symm
    _ ≤ _ := card_le_card sub

theorem total_le_junction_drop (acy : (Budget.G F).IsAcyclic) :
    total F ≤ Budget.classes (skeleton F) - Budget.classes F := by
  have h := Budget.exits_join_rank F acy
  have le := total_le_exits F acy
  omega

end GridGraphs.NoPitch.FaceJoin
