import GridGraphs.NoPitch.FiniteRows.Rest22
import GridGraphs.NoPitch.FiniteRows.Check22
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual
attribute [local irreducible] chart22
theorem checks22 : Checks chart22 7 scheme22 :=
  ⟨columnChecks22.1,columnChecks22.2.1,columnChecks22.2.2.1,columnChecks22.2.2.2,
   partition22,norm22,incidence22,fp22,faceLine22,flow22,letters22⟩
theorem feasible22 (F : Finset (Site 7)) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) :
    Feasible chart22 (physicalVector chart22 F (out F)) 8 0 (8*22^2) :=
  feasible (by decide) _ _ checks22 F acy np
end GridGraphs.NoPitch.FiniteRows

namespace GridGraphs
open NoPitch.FiniteRows
theorem maxPreserved_22_22 : maxPreserved 22 22 = 182 :=
  NoPitch.FiniteRows.exact (w:=.n22) (by decide) (by decide) scheme22 checks22
end GridGraphs
