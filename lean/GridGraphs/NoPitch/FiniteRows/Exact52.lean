import GridGraphs.NoPitch.FiniteRows.Rest52
import GridGraphs.NoPitch.FiniteRows.Check52
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual
attribute [local irreducible] chart52
theorem checks52 : Checks chart52 17 scheme52 :=
  ⟨columnChecks52.1,columnChecks52.2.1,columnChecks52.2.2.1,columnChecks52.2.2.2,
   partition52,norm52,incidence52,fp52,faceLine52,flow52,letters52⟩
theorem feasible52 (F : Finset (Site 17)) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) :
    Feasible chart52 (physicalVector chart52 F (out F)) 8 0 (8*52^2) :=
  feasible (by decide) _ _ checks52 F acy np
end GridGraphs.NoPitch.FiniteRows

namespace GridGraphs
open NoPitch.FiniteRows
theorem maxPreserved_52_52 : maxPreserved 52 52 = 955 :=
  NoPitch.FiniteRows.exact (w:=.n52) (by decide) (by decide) scheme52 checks52
end GridGraphs
