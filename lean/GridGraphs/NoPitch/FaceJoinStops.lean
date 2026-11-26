import GridGraphs.NoPitch.Budget.JunctionRank
import GridGraphs.NoPitch.PhysicalWiring

/-! Trace the *same* full-forest parent in the skeleton alone or in
the skeleton plus a single face. Each charged stop is a physical exit. -/
namespace GridGraphs.NoPitch.FaceJoin
open Finset SimpleGraph PitchCut
variable {k : Nat} (F : Finset (Site k))

def box (p : FacePos k) (x : Site k) : Prop :=
  3*p.1.val ≤ x.1.val ∧ x.1.val ≤ 3*p.1.val+3 ∧
  3*p.2.val ≤ x.2.val ∧ x.2.val ≤ 3*p.2.val+3

private theorem descent {x : Site k} (ne : Budget.parent F x≠x) :
    CapBill.depth (Budget.anchor F) (Budget.parent F x)<CapBill.depth (Budget.anchor F) x :=
  (CapBill.parent_step _ (Budget.sectionRoot F) (mt (CapBill.parent_fix _ _ x).mpr ne)).2

attribute [local instance] Classical.propDecidable
noncomputable def stop (A : Site k → Prop) (x : Site k) : Site k :=
  if _h : A x ∧ Budget.parent F x≠x then stop A (Budget.parent F x) else x
termination_by CapBill.depth (Budget.anchor F) x
decreasing_by exact descent F _h.2

theorem stop_terminal (A : Site k → Prop) (x : Site k) :
    ¬(A (stop F A x) ∧ Budget.parent F (stop F A x)≠stop F A x) := by
  rw [stop]; split
  next h => exact stop_terminal A (Budget.parent F x)
  next h => exact h
termination_by CapBill.depth (Budget.anchor F) x
decreasing_by apply descent; grind

abbrev oldStep (x : Site k) := (Budget.base F).Adj x (Budget.parent F x)
def localStep (p : FacePos k) (x : Site k) := oldStep F x ∨
  (box p x ∧ box p (Budget.parent F x))
attribute [local instance] Classical.propDecidable
noncomputable abbrev before (x : Site k) := stop F (oldStep F) x
noncomputable abbrev after (p : FacePos k) (x : Site k) := stop F (localStep F p) x

theorem old_reach_stop (x : Site k) : (Budget.base F).Reachable x (before F x) := by
  unfold before; rw [stop]; split
  next h => exact h.1.reachable.trans (old_reach_stop (Budget.parent F x))
  next => exact .rfl
termination_by CapBill.depth (Budget.anchor F) x
decreasing_by apply descent; grind

private theorem equal_on_edge (A : Site k → Prop) (x y : Site k)
    (acy : (Budget.G F).IsAcyclic) (e : (Budget.G F).Adj x y)
    (left : Budget.parent F x=y → A x) (right : Budget.parent F y=x → A y) :
    stop F A x=stop F A y := by
  rcases CapBill.parent_covers _ (Budget.sectionRoot F) acy e with h|h
  · change Budget.parent F x=y at h
    rw [stop.eq_def F A x, dif_pos ⟨left h,by rw [h]; exact e.ne.symm⟩,h]
  · change Budget.parent F y=x at h
    rw [stop.eq_def F A y, dif_pos ⟨right h,by rw [h]; exact e.ne⟩,h]

theorem base_le : Budget.base F ≤ Budget.G F :=
  forcedEdgeGraph_mono _ (fun _ h => (mem_filter.mp h).1)

private theorem const_reach {α β : Type*} {G : SimpleGraph α} (f : α → β)
    (edge : ∀ x y, G.Adj x y → f x=f y) {x y} (h : G.Reachable x y) : f x=f y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons e _ ih => exact (edge _ _ e).trans ih

theorem before_eq (acy : (Budget.G F).IsAcyclic) {x y} (r : (Budget.base F).Reachable x y) :
    before F x=before F y := by
  apply const_reach _ _ r
  intro a b e
  exact equal_on_edge F (oldStep F) _ _ acy (base_le F e)
    (fun h => by simpa [oldStep,h] using e) (fun h => by simpa [oldStep,h] using e.symm)

theorem after_eq (p : FacePos k) (acy : (Budget.G F).IsAcyclic)
    {x y} (r : (Budget.base F).Reachable x y) : after F p x=after F p y := by
  apply const_reach _ _ r
  intro a b e
  exact equal_on_edge F _ _ _ acy (base_le F e)
    (fun h => .inl (by simpa [oldStep,h] using e)) (fun h => .inl (by simpa [oldStep,h] using e.symm))

theorem after_edge (p : FacePos k) (acy : (Budget.G F).IsAcyclic) {x y}
    (bx : box p x) (by' : box p y) (e : (Budget.G F).Adj x y) : after F p x=after F p y :=
  equal_on_edge F _ _ _ acy e (fun h => .inr ⟨bx,h ▸ by'⟩) (fun h => .inr ⟨by',h ▸ bx⟩)

noncomputable def charges (p : FacePos k) := (Budget.exits F).filter fun x =>
  box p x ∧ box p (Budget.parent F x)

theorem unchanged (p : FacePos k) (acy : (Budget.G F).IsAcyclic) {x}
    (joint : x∈Budget.joints k) (free : before F x∉charges F p) :
    after F p x=before F x := by
  classical
  let z := before F x
  have reach := old_reach_stop F x
  rw [after_eq F p acy reach]
  change stop F (localStep F p) z=z
  rw [stop]; apply dif_neg
  rintro ⟨h,ne⟩
  have no : ¬oldStep F z := fun old => stop_terminal F _ x ⟨old,ne⟩
  apply free
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨?_,ne,no⟩,h.resolve_left no⟩
  apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
  by_cases eq : z=x
  · exact .inl (show z∈Budget.joints k by rw [eq]; exact joint)
  · have first {a b : Site k} (w : (Budget.base F).Walk a b) (h : a≠b) :
        ∃ u, (Budget.base F).Adj a u := by cases w with
        | nil => contradiction
        | cons e _ => exact ⟨_,e⟩
    exact .inr (first reach.symm.some eq)

end GridGraphs.NoPitch.FaceJoin
