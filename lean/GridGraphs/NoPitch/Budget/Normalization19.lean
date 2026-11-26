import GridGraphs.NoPitch.Budget.LocalBoard19
import GridGraphs.NoPitch.FaceRows

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset
attribute [local irreducible] chart19

def normRow (i : Nat) := 1 ≤ i && i ≤ 12
def blankStar (x : X) := localStar x false (fun _ => false) none
def blankPatch (p : P) := patchCode p (fun _ => false)
def normOK (D : Chart) :=
  let m := index D
  let sig : Array FaceRows.Terms := D.cols.map fun c => c.terms.filter (fun t => normRow t.1) |>.map (fun t => (t.1,t.2*(c.units:Int)))
  let w := FaceRows.contribution D m sig
  decide (∀ x bits f o, permissible x bits f o → w (localStar x f bits o)=w (blankStar x)) &&
  decide (∀ p a, legal a → w (patchCode p a)=w (blankPatch p))
def baseOK (D : Chart) :=
  let m := index D
  decide (∀ i : Fin D.rows.size, normRow i →
    2*((∑ x, lookupPrice D i m (blankStar x))+(∑ p, lookupPrice D i m (blankPatch p))) =
      8*D.rows[i].rhs.atStep 0)

private theorem ok19 : normOK chart19 := by native_decide
private theorem base19 : baseOK chart19 := by native_decide
private theorem support19 : supported chart19 normRow := by native_decide

private theorem sig_coeff (s : Nat → Bool) (i : Nat) (hi : s i) (ts : List (Nat × Int)) (u : Nat) :
    coeff i ((ts.filter fun p => s p.1).map (fun t => (t.1,t.2*u)))=coeff i ts*u := by
  induction ts with
  | nil => simp [coeff]
  | cons p ts ih =>
    by_cases e : p.1=i
    · simp [e,hi,coeff,add_mul] at ih ⊢; omega
    · cases h : s p.1 <;> simp [h,e,coeff] at ih ⊢ <;> exact ih

def prices (D : Chart) (s : Nat → Bool) : Array FaceRows.Terms := D.cols.map fun c =>
  (c.terms.filter fun t => s t.1).map (fun t => (t.1,t.2*(c.units:Int)))
theorem sig_price (D : Chart) (s : Nat → Bool) (i : Nat) (hi : s i) (key : Nat) :
    coeff i (FaceRows.contribution D (index D) (prices D s) key)=lookupPrice D i (index D) key := by
  unfold FaceRows.contribution lookupPrice
  cases e : locate D (index D) key with
  | none => rfl
  | some j => simpa [prices,j.isLt] using sig_coeff s i hi D.cols[j].terms D.cols[j].units

theorem normalization19 (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin chart19.rows.size)
    (h : normRow i) : 2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ok19
  let w := FaceRows.contribution chart19 (index chart19) (prices chart19 normRow)
  have st (x : X) : w (Keys.star F (out F) x)=w (blankStar x) := by
    rw [←star_agrees]
    exact of_decide_eq_true a x _ _ _ (physical_perm F acy x)
  have pa (p : P) : w (patch F p)=w (blankPatch p) := of_decide_eq_true b p _ (patch_legal F acy p)
  have eq (u : Nat) := sig_price chart19 normRow i h u
  change ∀ u, coeff i (w u)=_ at eq
  rw [star_patch_lhs support19 _ _ i h]
  simp only [←eq,st,pa]
  simp only [eq]
  exact of_decide_eq_true base19 i h

end GridGraphs.NoPitch.LocalBoard19
