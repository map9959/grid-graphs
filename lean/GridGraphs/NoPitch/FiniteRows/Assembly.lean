import GridGraphs.NoPitch.FiniteRows.Normalization
import GridGraphs.NoPitch.FiniteRows.Residual
import GridGraphs.NoPitch.FiniteRows.LineRows
import GridGraphs.NoPitch.FiniteRows.FacePatch
import GridGraphs.NoPitch.FiniteRows.FaceLine
import GridGraphs.Tests.CapSiteTableReplay
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget Keys GridGraphs.NoPitch.Dual TailRows

def byTag (tags : Array Nat) (t i : Nat) := tags[i]! == t
structure Scheme where
  inc : Incidence.Book
  fl : FaceLine.Book

@[noinline] def partitionOK (D : Chart) (s : Scheme) (tags : Array Nat) :=
  decide (∀ i : Fin D.rows.size, i.val=0 ∨ norms s.inc.start i ∨ s.inc.sel i ∨
    tags[i.val]! = 8 ∨ tags[i.val]! = 9 ∨ tags[i.val]! = 6 ∨ tags[i.val]! = 12) &&
  decide (∀ i : Fin D.rows.size, i.val≠0 → D.rows[i].sense=0 ∧ (¬norms s.inc.start i → D.rows[i].rhs=⟨0,0,0⟩))

def Checks (D : Chart) (k : Nat) (s : Scheme) : Prop :=
  checkClean D k ∧ fixedStarOnly D ∧ checkCorner D (N k) ∧ residualOK D ∧
  partitionOK D s (supportMasks D) ∧ normCheck D k s.inc.start ∧
  Incidence.cert D s.inc k ∧ FacePatch.cert D k ∧ FaceLine.cert D s.fl k ∧
  certified D k (byTag (supportMasks D) 8) ∧ certLetters D k (byTag (supportMasks D) 9)

theorem feasible {k} (hk : 7≤k) (D : Chart) (s : Scheme) (ok : Checks D k s)
    (F : Finset (Site k)) (acy : (G F).IsAcyclic) (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) :
    Feasible D (physicalVector D F (out F)) 8 0 (8*(N k:Int)^2) := by
  obtain ⟨cl,fx,cr,cap,partition,nm,inc,fp,fl,fc,lc⟩ := ok
  have r j : ¬Pitch F (teeth k j) := fun p => np _ (Or.inl p)
  have c j : ¬Pitch (trans F) (teeth k j) := fun p => np _ (Or.inr p)
  refine ⟨physical_nonneg D F (out F),fun j => physical_forbidden F cl fx j,bounded D cap F _ ,?_⟩
  intro i
  by_cases root : i.val=0
  · obtain ⟨j,hj,h⟩ := decoded_corner (b:=k) cr (by omega) F (by omega) acy 0
    exact (Fin.ext (hj.trans root.symm) : j=i) ▸ h
  by_cases norm : norms s.inc.start i
  · exact normalization hk D nm F acy i norm
  obtain ⟨p,m⟩ := Bool.and_eq_true_iff.mp partition
  obtain ⟨sense,rhs⟩ := of_decide_eq_true m i root
  have useZero (z : lhs D (physicalVector D F (out F)) i=0) :
      rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (out F)) i) (8*D.rows[i].rhs.atStep 0) := by
    rw [sense,rhs norm,z]; simp [rowHolds,Poly.atStep]
  by_cases range : s.inc.sel i
  · exact useZero (incidence hk D s.inc inc F acy i range)
  rcases of_decide_eq_true p i with h|h|h|f|l|a|t
  · contradiction
  · contradiction
  · contradiction
  · exact flow fc hk F r c _ i (beq_iff_eq.mpr f) 0
  · exact letters hk D _ lc F acy r c i (beq_iff_eq.mpr l) 0
  · exact useZero (FacePatch.Finite.facePatch hk D fp F acy _ i (beq_iff_eq.mpr a))
  · exact useZero (faceLine fl hk F acy r c _ i t)

theorem exact {w : Width} (small : w.k<19) (hk : 7≤w.k) (s : Scheme) (ok : Checks w.chart w.k s) :
    maxPreserved (N w.k) (N w.k)=squareScore (N w.k) := by
  apply exact_of_no_pitch_verified (by omega)
  intro F hf _ np
  have acy := mem_acyclicForcedSets.mp hf
  exact physical_finite_upper w small F acy _ (out_inside F) (feasible hk _ s ok F acy np)
end GridGraphs.NoPitch.FiniteRows
