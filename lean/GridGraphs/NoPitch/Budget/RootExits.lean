import GridGraphs.NoPitch.Budget.SkeletonMarks
import GridGraphs.Geometry.CapRootArrows

namespace GridGraphs.NoPitch.Budget
open SimpleGraph Finset PitchCut
open scoped Sym2
variable {k : Nat}
abbrev G (F : Finset (Site k)) := forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)
abbrev base (F : Finset (Site k)) := G (skeleton F)
def joints (k : Nat) := univ.filter (fun x : Site k => x.1.val%3=0 ∧ x.2.val%3=0)
attribute [local instance] Classical.propDecidable
noncomputable def oldSites (F : Finset (Site k)) :=
  univ.filter fun x => x∈joints k ∨ ∃ y, (base F).Adj x y

private theorem near_joint (F : Finset (Site k)) {x : Site k} (hx : x∈skeleton F) :
    ∃ y∈joints k, (base F).Reachable x y := by
  let y : Site k := (teeth k (owner x.1),teeth k (owner x.2))
  have vals : y.1.val=3*((x.1.val+1)/3) ∧ y.2.val=3*((x.2.val+1)/3) := ⟨rfl,rfl⟩
  refine ⟨y,mem_filter.mpr ⟨mem_univ _,by omega⟩,?_⟩
  by_cases h : x=y
  · rw [h]
  · have d := (mem_filter.mp hx).2
    have e : (gridGraph (N k) (N k)).Adj x y := by
      change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
      simp only [Prod.ext_iff,Fin.ext_iff] at h
      omega
    exact (show (base F).Adj x y from ⟨e,.inl hx⟩).reachable

theorem old_reaches (F : Finset (Site k)) {x} (old : x∈oldSites F) :
    ∃ y∈joints k, (base F).Reachable x y := by
  rcases (mem_filter.mp old).2 with h|⟨z,e⟩
  · exact ⟨_,h,.rfl⟩
  · rcases e.2 with h|h
    · exact near_joint F h
    · obtain ⟨y,hy,r⟩ := near_joint F h
      exact ⟨_,hy,e.reachable.trans r⟩

private theorem sub (F : Finset (Site k)) : base F ≤ G F :=
  forcedEdgeGraph_mono _ (by intro x hx; exact (mem_filter.mp hx).1)

def origin (k : Nat) : Site k := (teeth k 0,teeth k 0)
private theorem origin_joint : origin k∈joints k := mem_filter.mpr ⟨mem_univ _,⟨rfl,rfl⟩⟩
noncomputable abbrev anchor (F : Finset (Site k)) :=
  CapBill.chooseRoot (G F) {origin k} (joints k)
abbrev sectionRoot (F : Finset (Site k)) := CapBill.root_class (G F) {origin k} (joints k)
noncomputable def parent (F : Finset (Site k)) := CapBill.parent (anchor F) (sectionRoot F)
noncomputable def sinks (F : Finset (Site k)) := (joints k).filter fun x => parent F x=x
noncomputable def exits (F : Finset (Site k)) :=
  (oldSites F).filter fun x => parent F x≠x ∧ ¬(base F).Adj x (parent F x)

theorem picked (F : Finset (Site k)) {x z : Site k} (hz : z∈joints k)
    (eq : (G F).connectedComponentMk z=(G F).connectedComponentMk x) :
    CapBill.dest (anchor F) x ∈ joints k := by
  have h : ∃ v∈joints k, (G F).connectedComponentMk v=(G F).connectedComponentMk x := ⟨_,hz,eq⟩
  unfold CapBill.dest anchor CapBill.chooseRoot
  split
  next ht => rw [mem_singleton.mp ht.choose_spec.1]; exact origin_joint
  next => simpa only [dif_pos h] using h.choose_spec.1

theorem parent_origin (F : Finset (Site k)) : parent F (origin k)=origin k := by
  apply (CapBill.parent_fix _ _ _).mpr
  have h : ∃ v∈({origin k} : Finset (Site k)), (G F).connectedComponentMk v=
      (G F).connectedComponentMk (origin k) := ⟨_,mem_singleton_self _,rfl⟩
  simpa only [CapBill.dest,anchor,CapBill.chooseRoot,dif_pos h] using (mem_singleton.mp h.choose_spec.1).symm

theorem no_bad_sink (F : Finset (Site k)) {x} (hx : x∈oldSites F) (fix : parent F x=x) :
    x∈joints k := by
  obtain ⟨z,hz,r⟩ := old_reaches F hx
  exact (CapBill.parent_fix _ _ x).mp fix ▸ picked F hz (ConnectedComponent.sound ((r.mono (sub F)).symm))

theorem positive_sink (F : Finset (Site k)) : 0<(sinks F).card := by
  let x : Site k := (teeth k 0,teeth k 0)
  have hx : x∈joints k := mem_filter.mpr ⟨mem_univ _,⟨rfl,rfl⟩⟩
  let z := CapBill.dest (anchor F) x
  apply card_pos.mpr
  exact ⟨z,mem_filter.mpr ⟨picked F hx rfl,(CapBill.parent_fix _ _ z).mpr
    (by simp only [z,CapBill.dest,sectionRoot F _])⟩⟩

/-- The oriented edge ledger uses the same full-forest parent for every
base component. Isolated junctions are included in `oldSites`. -/
theorem exits_euler (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    (sinks F).card + (exits F).card + (base F).edgeFinset.card = (oldSites F).card := by
  classical
  let B := (oldSites F).filter fun x => (base F).Adj x (parent F x)
  have image : B.image (fun x => s(x,parent F x))=(base F).edgeFinset := by
    ext e; induction e using Sym2.inductionOn with | _ x y =>
      simp only [mem_image,mem_edgeFinset,mem_edgeSet]
      constructor
      · rintro ⟨v,h,eq⟩
        rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (mem_filter.mp h).2
        · exact (mem_filter.mp h).2.symm
      · intro e
        have old {a b} (t : (base F).Adj a b) : a∈oldSites F := mem_filter.mpr ⟨mem_univ _,.inr ⟨b,t⟩⟩
        rcases CapBill.parent_covers _ (sectionRoot F) acy (sub F e) with h|h
        · change parent F x=y at h
          exact ⟨x,mem_filter.mpr ⟨old e,h.symm ▸ e⟩,by rw [h]⟩
        · change parent F y=x at h
          exact ⟨y,mem_filter.mpr ⟨old e.symm,h.symm ▸ e.symm⟩,by rw [h,Sym2.eq_swap]⟩
  have inject : Set.InjOn (fun x => s(x,parent F x)) ↑B := by
    intro x hx y hy eq
    rcases Sym2.eq_iff.mp eq with h|⟨a,b⟩
    · exact h.1
    · have step {v} (hv : v∈B) := (CapBill.parent_step _ (sectionRoot F)
          (mt (CapBill.parent_fix _ _ v).mpr (mem_filter.mp hv).2.ne.symm)).2
      have p := step hx
      have q := step hy
      change CapBill.depth _ (parent F x)<_ at p
      change CapBill.depth _ (parent F y)<_ at q
      rw [b] at p; rw [←a] at q; omega
  have count := congrArg Finset.card image
  rw [card_image_of_injOn inject] at count
  have part := card_filter_add_card_filter_not (s:=oldSites F) (p:=fun x => parent F x=x)
  have part₂ := card_filter_add_card_filter_not (s:=(oldSites F).filter (fun x => parent F x≠x))
    (p:=fun x => (base F).Adj x (parent F x))
  have roots : (sinks F)=(oldSites F).filter fun x => parent F x=x := by
    ext x; simp only [sinks,mem_filter]
    exact ⟨fun ⟨h,f⟩ => ⟨mem_filter.mpr ⟨mem_univ _,.inl h⟩,f⟩,
      fun ⟨h,f⟩ => ⟨no_bad_sink F h f,f⟩⟩
  have same : ((oldSites F).filter (fun x => parent F x≠x)).filter
      (fun x => (base F).Adj x (parent F x))=B := by
    ext x; simp [B,and_assoc]; exact fun _ e => e.ne.symm
  rw [same,filter_filter] at part₂
  change _+(exits F).card=_ at part₂
  rw [←roots] at part
  rw [←count,add_assoc,add_comm (exits F).card,part₂]
  exact part

end GridGraphs.NoPitch.Budget
