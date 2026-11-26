import GridGraphs.NoPitch.Budget.PhysicalLedger
import GridGraphs.NoPitch.PhysicalKeys
import GridGraphs.ResidueZero.PhysicalStar

namespace GridGraphs.NoPitch.Budget
open SimpleGraph Finset PitchCut
variable {k : Nat}

/-- Number of actual connected components containing at least one
junction; unmarked isolated junctions are included. -/
noncomputable def classes (F : Finset (Site k)) : Nat := by
  classical exact ((joints k).image (G F).connectedComponentMk).card

theorem sinks_classes (F : Finset (Site k)) : (sinks F).card=classes F := by
  classical
  let root := anchor F
  let cc := (G F).connectedComponentMk
  have sec := sectionRoot F
  have eq : sinks F=((joints k).image cc).image root := by
    ext x
    simp only [sinks,mem_filter,mem_image]
    constructor
    · rintro ⟨j,fix⟩
      exact ⟨cc x,⟨x,j,rfl⟩,((CapBill.parent_fix _ _ x).mp fix).symm⟩
    · rintro ⟨c,⟨z,hz,rfl⟩,rfl⟩
      constructor
      · exact picked F hz rfl
      · apply (CapBill.parent_fix _ _ _).mpr
        change root (cc z)=root (cc (root (cc z)))
        rw [show cc (root (cc z))=cc z from sec _]
  rw [eq,card_image_of_injective _ (Function.LeftInverse.injective sec)]
  rfl

theorem skeleton_idem (F : Finset (Site k)) : skeleton (skeleton F)=skeleton F := by
  ext; simp [skeleton]

theorem exits_join_rank (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    classes F+(exits F).card=classes (skeleton F) := by
  classical
  have sub : base F≤G F := forcedEdgeGraph_mono _ (by intro x hx; exact (mem_filter.mp hx).1)
  have e := exits_euler F acy
  have s := exits_euler (skeleton F) (acy.anti sub)
  have same : oldSites (skeleton F)=oldSites F := by simp only [oldSites,base,skeleton_idem]
  have zero : exits (skeleton F)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x m
    obtain ⟨f,no⟩ := (mem_filter.mp m).2
    have step := (CapBill.parent_step _ (sectionRoot (skeleton F))
      (mt (CapBill.parent_fix _ _ x).mpr f)).1
    change (G (skeleton F)).Adj x (parent (skeleton F) x) at step
    apply no
    change (G (skeleton (skeleton F))).Adj x _
    rw [skeleton_idem]; exact step
  rw [sinks_classes] at e
  rw [sinks_classes,zero,same] at s
  have be := congrArg (fun S : Finset (Site k) => (G S).edgeFinset.card) (skeleton_idem F)
  change (base (skeleton F)).edgeFinset.card=(base F).edgeFinset.card at be
  rw [be] at s
  simp only [card_empty,add_zero] at s
  omega

theorem class_budget (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    axisDebit F + axisDebit (trans F) + (F.card:Int) + classes (skeleton F) ≤
      (N k:Int)*(k+1) + (F \ skeleton F).card := by
  have h := physical_debit_budget F acy rows cols
  rw [sinks_classes] at h
  rw [←exits_join_rank F acy,Nat.cast_add,←add_assoc]; exact h

/-- Arrow in the exact option/direction convention used by `Keys.star`. -/
noncomputable def out (F : Finset (Site k)) (x : Site k) : Option (Fin 4) :=
  let d := ResidueZero.outDir x (parent F x)
  if h : d<4 then some ⟨d,h⟩ else none

theorem out_none (F : Finset (Site k)) (x : Site k) : out F x=none ↔ parent F x=x := by
  by_cases e : x=parent F x
  · simp [out,ResidueZero.outDir,e.symm]
  · have ne := Ne.symm e
    have h : ResidueZero.outDir x (parent F x)<4 := by
      unfold ResidueZero.outDir; rw [if_neg e]; split_ifs <;> decide
    simp [out,h,ne]

theorem out_points (F : Finset (Site k)) (x : Site k) (d : Fin 4) (m : d∈out F x) :
    Keys.probe x d.val=some (parent F x) := by
  have ne : parent F x≠x := by intro e; rw [(out_none F x).mpr e] at m; cases m
  have a := (CapBill.parent_step _ (sectionRoot F)
    (mt (CapBill.parent_fix _ _ x).mpr ne)).1.1
  change (gridGraph (N k) (N k)).Adj x (parent F x) at a
  have shift := ResidueZero.shift_out a
  have eq : d.val=ResidueZero.outDir x (parent F x) := by
    dsimp only [out] at m
    split at m
    · cases m; rfl
    · cases m
  simp only [ResidueZero.shift,ResidueZero.coord,←eq,Prod.ext_iff] at shift
  have r := (parent F x).1.isLt
  have c := (parent F x).2.isLt
  unfold Keys.probe
  unfold N at r c
  fin_cases d <;> norm_num at shift ⊢ <;>
    refine ⟨by omega,Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩ <;> dsimp <;> omega

theorem out_inside (F : Finset (Site k)) : ∀ x d, d∈out F x → (Keys.probe x d.val).isSome := by
  intro x d m; rw [out_points F x d m]; rfl

end GridGraphs.NoPitch.Budget
