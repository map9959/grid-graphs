import GridGraphs.NoPitch.Budget.RootExits

namespace GridGraphs.NoPitch.Budget
open SimpleGraph Finset PitchCut
open scoped Sym2
variable {k : Nat}
abbrev Seg (k : Nat) := Bool × J k × Fin k
def point (s : Seg k) (t : Fin 4) : Site k :=
  let x := (teeth k s.2.1,coord s.2.2 t)
  if s.1 then x.swap else x
def live (F : Finset (Site k)) (s : Seg k) :=
  ((base F).Adj (point s 0) (point s 1) ∧ (base F).Adj (point s 1) (point s 2) ∧
    (base F).Adj (point s 2) (point s 3))
instance (F : Finset (Site k)) (s : Seg k) : Decidable (live F s) := by unfold live; infer_instance
def liveSegs (F : Finset (Site k)) := univ.filter (live F)
def onRim (x : Site k) := x.1.val%3=0 ∨ x.2.val%3=0
def isJoint (x : Site k) := x.1.val%3=0 ∧ x.2.val%3=0
instance (x : Site k) : Decidable (onRim x) := by unfold onRim; infer_instance
instance (x : Site k) : Decidable (isJoint x) := by unfold isJoint; infer_instance
def hub (x : Site k) : Site k := (teeth k (owner x.1),teeth k (owner x.2))
private theorem hub_joint (x : Site k) : isJoint (hub x) := by
  change 3*_ %3=0 ∧ 3*_ %3=0; simp
private theorem hub_adj (x : Site k) (r : onRim x) (j : ¬isJoint x) :
    (gridGraph (N k) (N k)).Adj x (hub x) := by
  change adjacent _ _ _ _; unfold adjacent
  simp only [Fin.ext_iff]
  have a : (hub x).1.val=3*((x.1.val+1)/3) := rfl
  have b : (hub x).2.val=3*((x.2.val+1)/3) := rfl
  unfold onRim isJoint at *; omega

/-- A midpoint uses its radial edge if present; otherwise it points to a
marked skeleton neighbour. An off-rim point always uses the latter rule. -/
noncomputable def target (F : Finset (Site k)) (x : Site k) :=
  if (base F).Adj x (hub x) then hub x
  else if h : ∃ y∈skeleton F, (base F).Adj x y then h.choose else x

private theorem target_spec (F : Finset (Site k)) {x}
    (hx : x∈oldSites F) (nj : ¬isJoint x) :
    (base F).Adj x (target F x) ∧
      ((target F x=hub x ∧ isJoint (target F x)) ∨
        (x∉skeleton F ∧ target F x∈skeleton F ∧ ¬(base F).Adj x (hub x))) := by
  have nx : x∉joints k := fun m => nj (mem_filter.mp m).2
  obtain ⟨y,adj⟩ := ((mem_filter.mp hx).2).resolve_left nx
  unfold target
  split
  next e => exact ⟨e,.inl ⟨rfl,hub_joint _⟩⟩
  next no =>
    have xm : x∉skeleton F := fun h => no ⟨hub_adj x (mem_filter.mp h).2 nj,.inl h⟩
    have h : ∃ y∈skeleton F, (base F).Adj x y := ⟨y,adj.2.resolve_left xm,adj⟩
    simp only [dif_pos h]
    exact ⟨h.choose_spec.2,.inr ⟨xm,h.choose_spec.1,no⟩⟩

def midEdge (s : Seg k) := s(point s 1,point s 2)
private theorem coord_eq (s : Seg k) (t : Fin 4) :
    ((point s t).1.val,(point s t).2.val)=
    (if s.1 then (3*s.2.2.val+t.val,3*s.2.1.val) else (3*s.2.1.val,3*s.2.2.val+t.val)) := by
  cases s with | mk b p => cases b <;> rfl

theorem mid_inj : Function.Injective (midEdge (k:=k)) := by
  rintro ⟨a,i,j⟩ ⟨b,u,v⟩ h
  rcases Sym2.eq_iff.mp h with ⟨h,_⟩|⟨h,_⟩ <;>
    apply_fun (fun x : Site k => (x.1.val,x.2.val)) at h <;>
    simp only [coord_eq] at h <;> cases a <;> cases b <;>
    simp_all [Prod.ext_iff,Fin.ext_iff] <;> omega

theorem live_mid (F : Finset (Site k)) {s} (h : live F s) (t : Fin 4) (ht : t=1 ∨ t=2) :
    ¬isJoint (point s t) ∧ (base F).Adj (point s t) (hub (point s t)) := by
  rcases s with ⟨b,i,j⟩
  obtain ⟨a,_,c⟩ := h
  have tooth (u : J k) : (teeth k u).val=3*u.val := rfl
  rcases ht with rfl|rfl
  · cases b <;> constructor
    all_goals first
      | simp [isJoint,point,coord,tooth,Nat.add_mod]; done
      | convert a.symm using 1
        simp [Prod.ext_iff,Fin.ext_iff,point,coord,hub,tooth,owner]; omega
  · cases b <;> constructor
    all_goals first
      | simp [isJoint,point,coord,tooth,Nat.add_mod]; done
      | convert c using 1
        simp [Prod.ext_iff,Fin.ext_iff,point,coord,hub,tooth,owner]; omega

noncomputable def ledgerEdges (F : Finset (Site k)) :=
  (oldSites F \ joints k).image (fun x => s(x,target F x)) ∪ (liveSegs F).image midEdge

theorem ledgerEdges_count (F : Finset (Site k)) :
    (ledgerEdges F).card=(oldSites F \ joints k).card + (liveSegs F).card := by
  classical
  let A := oldSites F \ joints k
  let edgeOf (x : Site k) := s(x,target F x)
  have data {x} (m : x∈A) := target_spec F (mem_sdiff.mp m).1
    (fun j => (mem_sdiff.mp m).2 (mem_filter.mpr ⟨mem_univ _,j⟩))
  have nj {x} (m : x∈A) : ¬isJoint x := fun j => (mem_sdiff.mp m).2 (mem_filter.mpr ⟨mem_univ _,j⟩)
  have inj : Set.InjOn edgeOf ↑A := by
    intro x hx y hy eq
    rcases Sym2.eq_iff.mp eq with h|⟨a,b⟩
    · exact h.1
    · rcases (data hx).2 with h|h
      · exact False.elim (nj hy (b ▸ h.2))
      · rcases (data hy).2 with g|g
        · exact False.elim (nj hx (a.symm ▸ g.2))
        · exact False.elim (g.1 (b ▸ h.2.1))
  have dis : Disjoint (A.image edgeOf) ((liveSegs F).image midEdge) := by
    apply Finset.disjoint_left.mpr
    intro e p q
    obtain ⟨x,hx,rfl⟩ := mem_image.mp p
    obtain ⟨s,hs,eq⟩ := mem_image.mp q
    have z := live_mid F (mem_filter.mp hs).2
    rcases Sym2.eq_iff.mp eq with ⟨a,b⟩|⟨b,a⟩
    · rcases (data hx).2 with h|h
      · exact (z 2 (.inr rfl)).1 (b.symm ▸ h.2)
      · exact h.2.2 (a ▸ (z 1 (.inl rfl)).2)
    · rcases (data hx).2 with h|h
      · exact (z 1 (.inl rfl)).1 (b.symm ▸ h.2)
      · exact h.2.2 (a ▸ (z 2 (.inr rfl)).2)
  change (A.image edgeOf ∪ (liveSegs F).image midEdge).card=_
  rw [card_union_of_disjoint dis,card_image_of_injOn inj,card_image_of_injective _ mid_inj]

theorem ledgerEdges_sub (F : Finset (Site k)) : ledgerEdges F ⊆ (base F).edgeFinset := by
  intro e m
  rcases mem_union.mp m with p|q
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp p
    exact mem_edgeFinset.mpr (target_spec F (mem_sdiff.mp hx).1
      (fun j => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_univ _,j⟩))).1
  · obtain ⟨s,hs,rfl⟩ := mem_image.mp q; exact mem_edgeFinset.mpr (mem_filter.mp hs).2.2.1

theorem live_edge_budget (F : Finset (Site k)) :
    (oldSites F \ joints k).card + (liveSegs F).card ≤ (base F).edgeFinset.card := by
  rw [←ledgerEdges_count]; exact card_le_card (ledgerEdges_sub F)

end GridGraphs.NoPitch.Budget
