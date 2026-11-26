import GridGraphs.NoPitch.FiniteRows.Rest25
import GridGraphs.NoPitch.FiniteRows.Check25
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual
attribute [local irreducible] chart25
theorem checks25 : Checks chart25 8 scheme25 :=
  ⟨columnChecks25.1,columnChecks25.2.1,columnChecks25.2.2.1,columnChecks25.2.2.2,
   partition25,norm25,incidence25,fp25,faceLine25,flow25,letters25⟩
theorem feasible25 (F : Finset (Site 8)) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) :
    Feasible chart25 (physicalVector chart25 F (out F)) 8 0 (8*25^2) :=
  feasible (by decide) _ _ checks25 F acy np
end GridGraphs.NoPitch.FiniteRows

namespace GridGraphs
open NoPitch.FiniteRows
theorem maxPreserved_25_25 : maxPreserved 25 25 = 233 :=
  NoPitch.FiniteRows.exact (w:=.n25) (by decide) (by decide) scheme25 checks25
end GridGraphs
