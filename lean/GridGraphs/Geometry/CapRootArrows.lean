import GridGraphs.Geometry.CapColoredBill
import GridGraphs.Geometry.PitchCutRank

namespace GridGraphs.CapBill
open Finset SimpleGraph
open scoped Sym2

variable {V : Type*}

/-- Prefer a terminal in the component, then another mark, then any vertex.
Choice is per *whole* component, before splitting at a slit. -/
noncomputable def chooseRoot (H : SimpleGraph V) (T F : Finset V)
    (c : H.ConnectedComponent) : V := by
  classical
  exact if ht : ∃ v∈T, H.connectedComponentMk v=c then ht.choose
    else if hf : ∃ v∈F, H.connectedComponentMk v=c then hf.choose
    else c.out

theorem root_class (H : SimpleGraph V) (T F : Finset V) (c : H.ConnectedComponent) :
    H.connectedComponentMk (chooseRoot H T F c)=c := by
  classical
  unfold chooseRoot
  split_ifs with a b
  · exact a.choose_spec.2
  · exact b.choose_spec.2
  · exact Quot.out_eq _

private theorem root_terminal (H : SimpleGraph V) {T F : Finset V} {c : H.ConnectedComponent}
    (a : ∃ v∈T, H.connectedComponentMk v=c) : chooseRoot H T F c ∈ T := by
  classical
  simpa only [chooseRoot,dif_pos a] using a.choose_spec.1

private theorem root_mark (H : SimpleGraph V) {T F : Finset V} {c : H.ConnectedComponent}
    (sub : T⊆F) (a : ∃ v∈F, H.connectedComponentMk v=c) : chooseRoot H T F c ∈ F := by
  classical
  unfold chooseRoot
  split_ifs with ht
  · exact sub ht.choose_spec.1
  · exact a.choose_spec.1

variable {H : SimpleGraph V} (root : H.ConnectedComponent → V)
  (sectionRoot : ∀ c, H.connectedComponentMk (root c)=c)

def dest (v : V) := root (H.connectedComponentMk v)
noncomputable def depth (v : V) := H.dist v (dest root v)

include sectionRoot in
private theorem smaller {v : V} (nv : v≠dest root v) :
    ∃ w, H.Adj v w ∧ depth root w < depth root v := by
  have reach : H.Reachable v (dest root v) := ConnectedComponent.exact (sectionRoot _).symm
  obtain ⟨p,hp⟩ := reach.exists_walk_length_eq_dist
  generalize ht : dest root v = t at p hp nv
  cases p with
  | nil => contradiction
  | cons e tail =>
    have same := ConnectedComponent.sound e.reachable
    refine ⟨_,e,?_⟩
    unfold depth dest
    rw [←same]
    change H.dist _ (dest root v) < H.dist v (dest root v)
    rw [ht]
    have := H.dist_le tail
    simp only [Walk.length_cons] at hp
    omega

noncomputable def parent (v : V) : V := by
  classical
  exact if h : v=dest root v then v else (smaller root sectionRoot h).choose

theorem parent_step {v : V} (h : v≠dest root v) :
    H.Adj v (parent root sectionRoot v) ∧ depth root (parent root sectionRoot v)<depth root v := by
  classical
  simpa [parent,h] using (smaller root sectionRoot h).choose_spec

theorem parent_fix (v : V) : parent root sectionRoot v=v ↔ v=dest root v := by
  classical
  by_cases h : v=dest root v
  · exact ⟨fun _ => h, fun _ => by unfold parent; rw [dif_pos h]⟩
  · exact iff_of_false (parent_step root sectionRoot h).1.ne.symm h

include sectionRoot in
theorem fixed_count [Fintype V] [DecidableEq V] [DecidableRel H.Adj] :
    (univ.filter fun v => v=dest root v).card =
    Fintype.card H.ConnectedComponent := by
  classical
  have eq : (univ.filter fun v => v=dest root v) = univ.image root := by
    ext v; simp only [mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro h; exact ⟨_,h.symm⟩
    · rintro ⟨c,rfl⟩; simp [dest,sectionRoot]
  rw [eq,card_image_of_injective _ (Function.LeftInverse.injective sectionRoot),card_univ]

/-- The oriented parent edges exhaust the physical edges: injectivity by
strict descent; surjectivity by the forest ledger, not a path heuristic. -/
theorem parent_covers [Fintype V] (forest : H.IsAcyclic) {x y : V} (e : H.Adj x y) :
    parent root sectionRoot x=y ∨ parent root sectionRoot y=x := by
  classical
  let S := univ.filter fun v => ¬v=dest root v
  let p := parent root sectionRoot
  let edges := S.image (fun v => s(v,p v))
  have subset : edges ⊆ H.edgeFinset := by
    intro z hz; obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    exact mem_edgeFinset.mpr (parent_step root sectionRoot (mem_filter.mp hv).2).1
  have inj : Set.InjOn (fun v => s(v,p v)) ↑S := by
    intro u hu v hv eq
    rcases Sym2.eq_iff.mp eq with h|⟨h₁,h₂⟩
    · exact h.1
    · have a := (parent_step root sectionRoot (mem_filter.mp hu).2).2
      have b := (parent_step root sectionRoot (mem_filter.mp hv).2).2
      change depth root (p u) < _ at a
      change depth root (p v) < _ at b
      rw [h₂] at a; rw [←h₁] at b; omega
  have count := forest.card_edgeFinset_add_card_connectedComponent
  have split := card_filter_add_card_filter_not (s:=(univ : Finset V)) (p:= fun v => v=dest root v)
  rw [fixed_count root sectionRoot, card_univ] at split
  change _+S.card=_ at split
  have eq : edges=H.edgeFinset := eq_of_subset_of_card_le subset (by
    change _ ≤ (S.image _).card; rw [card_image_of_injOn inj]; omega)
  have mem : s(x,y) ∈ edges := eq ▸ (mem_edgeFinset.mpr e)
  obtain ⟨v,hv,eq⟩ := mem_image.mp mem
  rcases Sym2.eq_iff.mp eq with ⟨rfl,h⟩|⟨rfl,h⟩
  · exact Or.inl h
  · exact Or.inr h

section Charges
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (T F : Finset V)
private abbrev fg := forcedEdgeGraph G (↑F : Set V)
private noncomputable abbrev anchor := chooseRoot (fg G F) T F
noncomputable def keeps (v : V) := v=dest (anchor G T F) v
noncomputable def waived : Finset V := by classical exact T.filter fun v => ¬keeps G T F v
noncomputable def extraRoots : Finset V := by classical exact F.filter fun v => v∉T ∧ keeps G T F v

omit [Fintype V] in
theorem blank_fixed (sub : T⊆F) {v : V} (hv : v∉F) :
    keeps G T F v ↔ hits G F v=0 := by
  classical
  constructor
  · intro fix
    by_contra nonzero
    have ne : (F.filter fun w => G.Adj w v).Nonempty := by
      apply card_ne_zero.mp
      intro zero; exact nonzero (by simp [hits,zero])
    obtain ⟨w,hw⟩ := ne
    obtain ⟨wm,adj⟩ := mem_filter.mp hw
    have edge : (fg G F).Adj w v := ⟨adj,Or.inl wm⟩
    have inF := root_mark (fg G F) sub ⟨w,wm,ConnectedComponent.sound edge.reachable⟩
    exact hv (fix ▸ inF)
  · intro zero
    change v=dest (anchor G T F) v
    by_contra different
    have reach : (fg G F).Reachable v (dest (anchor G T F) v) :=
      ConnectedComponent.exact (root_class _ _ _ _).symm
    obtain ⟨w,e⟩ := mem_support_of_reachable different reach
    have wm : w ∈ F := e.2.resolve_left hv
    have has : (F.filter fun w => G.Adj w v).Nonempty := ⟨w,mem_filter.mpr ⟨wm,e.1.symm⟩⟩
    unfold hits at zero; exact (card_ne_zero.mpr has) (by exact_mod_cast zero)

theorem extras_count (sub : T⊆F) :
    ((extraRoots G T F).card : Int) =
    (Fintype.card (fg G F).ConnectedComponent : Int) - (∑ v, iso G F v) -
      ((T.card : Int)-(waived G T F).card) := by
  classical
  have sumFix : (∑ v : V, (if keeps G T F v then (1:ℤ) else 0)) =
      Fintype.card (fg G F).ConnectedComponent := by
    rw [sum_boole]
    norm_cast
    convert fixed_count (anchor G T F) (root_class _ _ _) using 1
    congr 1; apply Finset.filter_congr; intro v _; rfl
  have per (v : V) : (if keeps G T F v then (1:ℤ) else 0) =
      (if v∈extraRoots G T F then 1 else 0)+iso G F v+
      ((if v∈T then 1 else 0)-(if v∈waived G T F then 1 else 0)) := by
    by_cases ht : v∈T
    · have hf := sub ht
      by_cases hk : keeps G T F v <;> simp [extraRoots,iso,waived,ht,hf,hk]
    · by_cases hf : v∈F
      · simp [extraRoots,iso,waived,ht,hf]
      · simp [extraRoots,iso,waived,ht,hf,blank_fixed G T F sub hf]
  simp_rw [per] at sumFix
  simp only [sum_add_distrib,sum_sub_distrib,sum_boole,filter_mem_eq_inter,univ_inter] at sumFix
  omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem waived_eq_rank (Tₑ : Fin T.card ≃ ↥T) :
    (waived G T F).card = PitchCut.rank (fg G F) (fun i => (Tₑ i).val) := by
  classical
  let C := T.image (fg G F).connectedComponentMk
  have classes : PitchCut.classes (fg G F) (fun i => (Tₑ i).val) = C := by
    ext c; simp only [PitchCut.classes,C,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨_,(Tₑ i).property,rfl⟩
    · rintro ⟨v,hv,rfl⟩; exact ⟨Tₑ.symm ⟨v,hv⟩,by simp⟩
  have retained : T.filter (keeps G T F) = C.image (anchor G T F) := by
    ext v
    simp only [C,mem_filter,mem_image]
    constructor
    · rintro ⟨h,fix⟩
      exact ⟨_,⟨v,h,rfl⟩,fix.symm⟩
    · rintro ⟨c,h,rfl⟩
      exact ⟨root_terminal _ h,by simp [keeps,dest,anchor,root_class]⟩
  have c := card_filter_add_card_filter_not (s:=T) (p:=keeps G T F)
  rw [retained,card_image_of_injective _ (Function.LeftInverse.injective (root_class _ _ _))] at c
  rw [PitchCut.rank,classes,Fintype.card_fin]
  change C.card+(waived G T F).card=T.card at c
  omega

end Charges
end GridGraphs.CapBill
