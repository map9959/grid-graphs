import Mathlib

namespace GridGraphs.BoundaryInterfaceDebit

/-- In a strip of width 3l+1, count only marks outside the backing
column. The ideal value on those columns is lH. -/
theorem arbitraryDepth (excess bad holes rim ends runs comps : ℤ)
    (ledger : 3*excess = 2*holes-rim+ends-runs-comps)
    (triples : bad ≤ 3*runs+comps) (hc : 0 ≤ comps) :
    9*excess + bad + 3*rim ≤ 6*holes + 3*ends := by omega

/-- On an entire side an optimum cannot have negative excess since
the exterior can be replaced by l disjoint free bars. -/
theorem propagation (excess bad holes rim d : ℤ) (maximal : 0 ≤ excess)
    (debit : 9*excess + bad + 3*rim ≤ 6*holes + 6*(d+1)) :
    bad+3*rim-6*(d+1) ≤ 6*holes := by omega

/-- Thirty times the unrestricted real-sector slack at comb+1 is
k-26+3r. A full-side depth-six debit above it excludes that score. -/
theorem excludesGain (excess gain bad holes k r : ℤ)
    (sector : 30*(excess+gain-1) ≤ k-26+3*r)
    (surgery : 6*bad-24*holes-126 ≤ 30*gain)
    (enough : k-26+3*r < 6*bad-24*holes-126) : excess ≤ 0 := by omega

/-- Stack the all-depth inequalities over the first q aligned columns. -/
theorem totalHoles (q : ℕ) (holes : ℕ → ℤ) (bad : ℤ)
    (h : ∀ i < q, bad - 6*(3*((i:ℤ)+1)+1) ≤ 6*holes i) :
    (q:ℤ)*(bad-15-9*q) ≤ 6 * ∑ i ∈ Finset.range q, holes i := by
  induction q with
  | zero => simp
  | succ q ih =>
    have prev := ih (fun i hi => h i (by omega))
    have next := h q (by omega)
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- Cancel the common quadratic in the two-cut comparison.
`linear` is score minus 3k²; suppressing the exceptional -1 in
the residue-two upper only weakens the inequality. -/
theorem phaseLength (k F K linear gain : ℤ)
    (insert : 21*gain ≥ 98*(3*k+1)-4*F-21*(22*(K+2)+12))
    (neighbor : linear+gain ≤ 19*k+26-(k-3)/7) :
    210*(linear-5*k-(3*k-13)/10) ≤
      40*F-31*(3*k+1)+210*(22*K+81) := by omega

end GridGraphs.BoundaryInterfaceDebit
