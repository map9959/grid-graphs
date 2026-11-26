import GridGraphs.NoPitch.Budget.FixedReplay
import GridGraphs.NoPitch.TailStarCoverage

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys GridGraphs.NoPitch.Dual TailCoverage
attribute [local irreducible] chart19 chart58 chart61
variable {k : Nat}

private def shift (d : Nat) (plus minus : Nat) : Int := if d=plus then 1 else if d=minus then -1 else 0
private theorem translated {k t : Nat} {x : Site k} {y : Site t}
    (h : Match (3*k) (3*t) x.1.val x.2.val y.1.val y.2.val) (d : Nat) :
    ((probe x d).isSome=(probe y d).isSome) ∧
      (∀ p q, probe x d=some p → probe y d=some q → (onRim p ↔ onRim q)) := by
  have bound (a b : Nat) : -1 ≤ shift d a b ∧ shift d a b ≤ 1 := by
    unfold shift; split_ifs <;> decide
  have axisIn {k t i j : Nat} (a : Axis (3*k) (3*t) i j) (s : Int) (bd : -1 ≤ s ∧ s≤1) :
      (0≤(i:Int)+s ∧ ((i:Int)+s).toNat<N k) ↔ (0≤(j:Int)+s ∧ ((j:Int)+s).toNat<N t) := by
    rcases a with ⟨_,_,_,lo,hi⟩; unfold Sat at lo hi; unfold N; omega
  have r := axisIn h.row _ (bound 1 3)
  have c := axisIn h.col _ (bound 0 2)
  unfold shift at r c
  constructor
  · unfold probe; dsimp only
    simp only [apply_dite Option.isSome,Option.isSome_some,Option.isSome_none,dite_eq_ite]
    generalize (if d=1 then (1:Int) else if d=3 then -1 else 0)=u at r ⊢
    generalize (if d=0 then (1:Int) else if d=2 then -1 else 0)=v at c ⊢
    split <;> split <;> first | rfl | exfalso; tauto
  · intro p q u v
    unfold probe at u v
    simp only [Option.dite_none_right_eq_some,Option.some.injEq] at u v
    obtain ⟨hu,rfl⟩ := u; obtain ⟨hv,rfl⟩ := v
    unfold onRim
    have rr := h.row.residue; have cc := h.col.residue
    dsimp only
    split_ifs at * <;> omega

theorem checkClean_step {D : Chart} (hk : 19≤k) (baseCheck : checkClean D k) :
    checkClean D (k+2) := by
  unfold checkClean; rw [decide_eq_true_eq]
  intro x bits f o good
  obtain ⟨a,b,h⟩ := representative (m:=3*k) (by omega) (i:=x.1.val) (j:=x.2.val)
    (by have := x.1.isLt; unfold N at this; omega) (by have := x.2.isLt; unfold N at this; omega)
  let y : Site k := (⟨a,by have := h.row.dst; unfold N; omega⟩,⟨b,by have := h.col.dst; unfold N; omega⟩)
  have w : 3*(k+2)=3*k+6 := by omega
  have hm : Match (3*(k+2)) (3*k) x.1.val x.2.val y.1.val y.2.val := by
    change Match (3*(k+2)) (3*k) _ _ a b; rw [w]; exact h
  have joint : isJoint x ↔ isJoint y := by simp only [isJoint,hm.row.residue,hm.col.residue]
  have rim : onRim x ↔ onRim y := by simp only [onRim,hm.row.residue,hm.col.residue]
  have bv (d : Fin 4) : baseBit x f bits d=baseBit y f bits d := by
    have z := translated hm d.val
    unfold baseBit
    cases p : probe x d.val <;> cases q : probe y d.val
    · rfl
    · simp [p,q] at z
    · simp [p,q] at z
    · simp only [Option.any_some,rim,z.2 _ _ p q]
  have ob : oldBit x f bits=oldBit y f bits := by simp only [oldBit,joint,bv]
  have hit := of_decide_eq_true baseCheck y bits f o (fun s b => joint.mp (good s (ob ▸ b)))
  have eq : starCode (N (k+2)) x.1.val x.2.val (sampled x bits) o=
      starCode (N k) y.1.val y.2.val (sampled y bits) o := by
    unfold starCode; apply congrArg minimum; funext g
    simp only [N,hm.view w g,sampled,(translated hm _).1]
  simpa only [eq] using hit

private theorem clean_tail (hk : 19≤k) : checkClean (tailChart k) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k≤20
    · interval_cases k
      · exact clean58
      · exact clean61
    · have h₂ : k-2+2=k := by omega
      have b := checkClean_step (k:=k-2) (by omega) (ih (k-2) (by omega) (by omega))
      simpa [h₂,tailChart,show (k-2)%2=k%2 by omega] using b

theorem physical_forbidden {D : Chart} (F : Finset (Site k)) (ok : checkClean D k) (only : fixedStarOnly D)
    (j : Fin D.cols.size) (fix : D.cols[j].fixed) : physicalVector D F (out F) j=0 := by
  have stars (x : Site k) : locate D (index D) (Keys.star F (out F) x)≠some j := by
    have code : starCode (N k) x.1.val x.2.val (sampled x (bitsAt F x)) (out F x)=
        starCode (N k) x.1.val x.2.val (neighbor F x) (out F x) := by
      unfold starCode; apply congrArg minimum; funext g
      have eq (d : Nat) := sampled_bits F x (⟨direction (invers g) d,by unfold direction; omega⟩ : Fin 4)
      simp only [eq]
    have hit := of_decide_eq_true ok x (bitsAt F x) (decide (x∈F)) (out F x) (fun o h =>
      (mem_filter.mp (no_bad_sink F ((oldBit_iff ..).mp h) ((out_none F x).mp (Option.isNone_iff_eq_none.mp o)))).2)
    rw [code] at hit
    intro p
    change cleanKey D (index D) (Keys.star F (out F) x) at hit
    simp [cleanKey,p] at hit
    exact Bool.noConfusion (fix.symm.trans hit)
  have low : D.cols[j].key%8<2 := by
    have z := Array.all_eq_true_iff_forall_mem.mp only _ (Array.getElem_mem j.isLt)
    change (!D.cols[j].fixed || decide (D.cols[j].key%8<2))=true at z
    simpa only [fix,Bool.not_true,Bool.false_or,decide_eq_true_eq] using z
  have no (key : Nat) (h : 2≤key%8) : locate D (index D) key≠some j := by
    intro p; rw [←locate_key p] at h; omega
  have a (p : FacePos k) : locate D (index D) (face F p)≠some j := by
    apply no; unfold face faceCode keyAt; omega
  have b (t : Fin 8 × J k × J k) : locate D (index D) (line F t.1 t.2.1 t.2.2)≠some j := by
    apply no; unfold line; dsimp only; omega
  have c (p : PatchPos k) : locate D (index D) (patch F p)≠some j := by
    apply no; unfold patch patchCode; omega
  simp only [physicalVector,counts,scatter,if_neg (stars _),if_neg (a _),if_neg (b _),if_neg (c _),
    if_neg (by omega : D.cols[j].key%8≠5),sum_const_zero,add_zero]

theorem forbidden19 (F : Finset (Site 6)) (j : Fin chart19.cols.size) (fix : chart19.cols[j].fixed) :
    physicalVector chart19 F (out F) j=0 := physical_forbidden F clean19 fixed19 j fix
theorem forbidden_tail (F : Finset (Site k)) (hk : 19≤k) (j : Fin (tailChart k).cols.size)
    (fix : (tailChart k).cols[j].fixed) : physicalVector (tailChart k) F (out F) j=0 := by
  apply physical_forbidden F (clean_tail hk) _ j fix
  unfold tailChart; split <;> first | exact fixed58 | exact fixed61

end GridGraphs.NoPitch.Budget
