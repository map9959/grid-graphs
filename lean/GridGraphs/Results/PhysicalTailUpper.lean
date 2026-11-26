import GridGraphs.NoPitch.TailStarCoverage

namespace GridGraphs.NoPitch.TailCoverage
open GridGraphs.NoPitch.Dual PitchCut
attribute [local irreducible] chart58 chart61

/-- Uniform tail dual on the actual physical vector. Only feasibility
remains to be supplied by the geometric proof; the objective is derived. -/
theorem physical_tail_upper {k : Nat} (hk : 19 ≤ k) (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (Keys.probe x d.val).isSome)
    {cap : Int} (rows : Feasible (tailChart k) (physicalVector (tailChart k) F out)
      8 ((k-19)/2 : Nat) cap) : F.card ≤ squareScore (N k) := by
  have obj := objective_tail hk F acy out inside
  apply certified_tail hk cap
  by_cases odd : k%2=1
  · rw [show tailChart k=chart58 by simp [tailChart,odd]] at rows obj
    rw [if_pos odd]
    exact ⟨physicalVector chart58 F out,rows,obj⟩
  · rw [show tailChart k=chart61 by simp [tailChart,odd]] at rows obj
    rw [if_neg odd]
    exact ⟨physicalVector chart61 F out,rows,obj⟩

end GridGraphs.NoPitch.TailCoverage
