import GridGraphs.ResidueTwoUpper.TwoGapFrontierTrace
import GridGraphs.ResidueTwoUpper.TwoGapCoverageCert

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open ResidueZero Stencil Catalogue Words BoundarySix.Connected

private theorem top_word : ∀ (a b : Word), permits tables[0]! a b → a=(48,48,48) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ ⟨h₁,h₂⟩
  have top : tables[0]! = [(48,56,48,56)] := by native_decide
  rw [top] at h₁ h₂
  simp_all

/-- Conditional interface: the bands and the physical pushes here use
the same mark set and the same (unfolded) consecutive row coordinates. -/
theorem impossible_of_permits {u q} (F : Finset (Board u)) {P} (C : North.Chart F P (2+3*q))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    (lo : 3≤q) (hi : q+4≤bands u)
    (ok : ∀ j, j+1<bands u → permits tables[Coverage.level (bands u) j]!
      (physicalWordAt F q j) (physicalWordAt F q (j+1))) : False := by
  let k := bands u
  let w := physicalWordAt F q
  have sz : 11≤k := by dsimp [k,bands]; omega
  let inv (j : Nat) (states : List State) := ∃ s, (w j,s)∈states ∧
    Represents F (2+3*q) (leftCol q) (3*(j+1)) s
  have go {j xs} (h : inv j xs) (hj : j+1<k) :
      inv (j+1) (step tables[Coverage.level k j]! (toothNo k (j+1)) xs) := by
    obtain ⟨s,m,rep⟩ := h
    obtain ⟨z,p,rep'⟩ := physical_push F C acy score canon lo hi hj rep
    exact ⟨z,step_mem m (ok j hj) p,rep'⟩
  have start : inv 0 init := by
    have top : w 0=(48,48,48) := top_word _ _ (ok 0 (by omega))
    have W : StepWindow u (leftCol q) 0 := by constructor <;> dsimp [leftCol,bands,high] at * <;> omega
    obtain ⟨z,p,r⟩ := physical_push (j:=0) F C acy score canon lo hi (by omega) (initial_rep F _ _ W)
    change push base (w 0) 495=some z at p
    rw [top] at p
    exact ⟨z,by simp [init,p,top],r⟩
  have s1 : inv 1 (step tables[0]! 0 init) := by
    simpa [Coverage.level,toothNo,show 2≠k by omega] using go start (by omega)
  have s2 : inv 2 seed := by
    simpa [seed,Coverage.level,toothNo,show 3≠k by omega] using go s1 (by omega)
  have mid (r : Nat) (hr : r+5≤k) : inv (2+r) ((step tables[2]! 0)^[r] seed) := by
    induction r with
    | zero => exact s2
    | succ r ih =>
      have h := go (ih (by omega)) (by omega)
      have tag : Coverage.level k (2+r)=2 := by unfold Coverage.level; split_ifs <;> omega
      have tooth : toothNo k (2+r+1)=0 := by unfold toothNo; split_ifs <;> omega
      rw [tag,tooth] at h
      rw [Function.iterate_succ_apply']; exact h
  let a := k-6
  have end₁ : 2+(a+1)=k-3 := by dsimp [a]; omega
  have r := mid (a+1) (by dsimp [a]; omega)
  rw [end₁] at r
  have pre := go r (by omega)
  have t₃ : Coverage.level k (k-3)=3 := by unfold Coverage.level; split_ifs <;> omega
  have h₃ : toothNo k (k-3+1)=0 := by unfold toothNo; split_ifs <;> omega
  rw [t₃,h₃] at pre
  have done := go pre (by omega)
  have t₄ : Coverage.level k (k-3+1)=4 := by unfold Coverage.level; split_ifs <;> omega
  have h₄ : toothNo k (k-3+1+1)=511 := by
    rw [toothNo,if_neg (by omega),if_pos (by omega : k-3+1+1+1=k)]
  rw [t₄,h₄] at done
  change inv _ (accepted (a+1)) at done
  obtain ⟨s,h,_⟩ := done
  rw [replay_empty] at h
  exact List.not_mem_nil h

/-- The canonical ordinary `0011` two-gap case cannot attain the
exceptional target, including side 35 and every folded tail width. -/
theorem physical_0011_impossible {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    packed (signature (by omega) F) ≠ code4 0 0 1 1 := by
  intro canon
  obtain ⟨P,q,s,C,G,_,lo,hi,permit⟩ := Coverage.physical_catalogue F acy score two canon
  apply impossible_of_permits F C acy score canon lo hi
  intro j hj
  have eq (i j : Int) : stripWord s i j=stripWord (maskField F) i j := by
    simp [stripWord,tile,G.marks,maskField]
  have h := permit j hj
  rw [eq,eq] at h
  simpa [physicalWordAt,bands] using h

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
