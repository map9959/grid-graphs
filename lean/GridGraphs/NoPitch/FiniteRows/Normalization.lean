import GridGraphs.NoPitch.FiniteRows.Incidence
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget LocalBoard19 FaceRows GridGraphs.NoPitch.Dual Finset TailRows

def norms (stop i : Nat) := 1 ≤ i && i < stop

def emptyStar {k} (x : Site k) := sKey x false (fun _ => false) none
def emptyPatch {k} (p : PatchPos k) := patchCode p (fun _ => false)

@[noinline] def normalSites (k : Nat) (w : Nat → Terms) :=
  decide (∀ x : Site k, starNormAt w x (w (emptyStar x))) &&
    decide (∀ p : PatchPos k, patchNormAt w p (w (emptyPatch p)))

@[noinline] def normalTotals (D : Chart) (k stop : Nat) (w : Nat → Terms) :=
  let xs := Vector.ofFn (n:=N k) fun r => Vector.ofFn (n:=N k) fun c => w (emptyStar (k:=k) (r,c))
  let ps := Vector.ofFn (n:=N k-2) fun r => Vector.ofFn (n:=N k-2) fun c => w (emptyPatch (k:=k) (r,c))
  decide (∀ i : Fin D.rows.size, norms stop i → D.rows[i].sense=0 ∧
    2*((∑ x : Site k, coeff i xs[x.1][x.2])+(∑ p : PatchPos k, coeff i ps[p.1][p.2]))=8*D.rows[i].rhs.atStep 0)

def normCheck (D : Chart) (k stop : Nat) :=
  let w := contribution D (index D) (prices D (norms stop))
  supported D (norms stop) && normalSites k w && normalTotals D k stop w

theorem normalization {k stop} (hk : 7≤k) (D : Chart) (ok : normCheck D k stop)
    (F : Finset (Site k)) (acy : (G F).IsAcyclic) (i : Fin D.rows.size) (h : norms stop i) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (out F)) i) (8*D.rows[i].rhs.atStep 0) := by
  obtain ⟨first,tot⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨sup,checks⟩ := Bool.and_eq_true_iff.mp first
  obtain ⟨st,pa⟩ := Bool.and_eq_true_iff.mp checks
  let w := contribution D (index D) (prices D (norms stop))
  have S (x : Site k) : lookupPrice D i (index D) (Keys.star F (out F) x)=coeff i (w (emptyStar x)) := by
    have z := zero_of_balanced _ (of_decide_eq_true (of_decide_eq_true st x) _ _ _ (physical_admissible F acy x)) i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h,physical_sKey] at z; exact eq_of_sub_eq_zero z
  have P (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=coeff i (w (emptyPatch p)) := by
    have z := zero_of_balanced _ (of_decide_eq_true (of_decide_eq_true pa p) _ (legal_small F hk acy p)) i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h] at z; exact eq_of_sub_eq_zero z
  have m := of_decide_eq_true tot i h
  rw [m.1,starPatchLhs D _ sup F i h]; simp only [rowHolds,if_true,S,P]
  simpa only [Fin.getElem_fin,Vector.getElem_ofFn] using m.2
end GridGraphs.NoPitch.FiniteRows
