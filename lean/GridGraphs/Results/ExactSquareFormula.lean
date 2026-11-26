import GridGraphs.Results.DiagonalFormula
import GridGraphs.Results.SmallDiagonalExact
import GridGraphs.Results.WidthFourExact
import GridGraphs.Results.SmallDiagonal
import GridGraphs.Constructions.CombWord

/-! The corrected square formula from `docs/EXACT_SQUARE_FORMULA.md`.
`diagonalFormulaP` is the earlier conditional proposal, not this function.
The universal graph equality is a proposition; the reductions and range
theorems below are kernel proofs, not imports of external certificates. -/

namespace GridGraphs

/-- Predicted score for every positive square side; use zero on side zero. -/
def squareScore (n : ℕ) : ℕ :=
  let k := n / 3
  match n % 3 with
  | 0 => 3*k^2 + 3*k - 2
  | 1 =>
    if k = 0 then 1 else
      3*k^2 + 5*k + (3*k-13)/10
  | _ =>
    if k = 0 then 2 else if k < 5 then 3*k^2 + 7*k + 1 else
      3*k^2 + 7*k - (k-5)/7 - (if n%42 = 35 then 1 else 0)

/-- The full graph-theoretic statement, using the actual spanning-tree maximum. -/
def ExactSquareFormula : Prop := ∀ n, 0 < n → maxPreserved n n = squareScore n

@[simp] theorem squareScore_three_mul (k : ℕ) :
    squareScore (3*k) = 3*k^2+3*k-2 := by
  simp [squareScore, Nat.mul_comm 3 k]

@[simp] theorem squareScore_three_mul_add_one (k : ℕ) (hk : 0 < k) :
    squareScore (3*k+1) = 3*k^2+5*k+(3*k-13)/10 := by
  simp [squareScore, show (3*k+1)%3=1 by omega, show (3*k+1)/3=k by omega,
    Nat.ne_of_gt hk]

@[simp] theorem squareScore_three_mul_add_two (k : ℕ) (hk : 6 ≤ k) :
    squareScore (3*k+2) = 3*k^2+7*k-(k-5)/7-(if k%14=11 then 1 else 0) := by
  have phase : (3*k+2)%42=35 ↔ k%14=11 := by omega
  simp [squareScore, show (3*k+2)%3=2 by omega, show (3*k+2)/3=k by omega,
    show k ≠ 0 by omega, show ¬k<5 by omega, phase]

/-- A mask certificate consists entirely of grid vertices and an acyclicity
proof for their incident grid edges, without choosing a completion tree. -/
def SquareMaskScore (n s : ℕ) : Prop :=
  ∃ F ∈ acyclicForcedSets n n, F.card = s

theorem squareMaskScore_down {n a b : ℕ} (h : SquareMaskScore n b) (hab : a ≤ b) :
    SquareMaskScore n a := by
  obtain ⟨F,hF,rfl⟩ := h
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hab
  exact ⟨S,mem_acyclicForcedSets.mpr ((mem_acyclicForcedSets.mp hF).anti
    (forcedEdgeGraph_mono _ (by exact_mod_cast hS))),hcard⟩

/-- Exact-size search suffices on both sides: there is no need to exclude
each larger size separately. This equivalence uses no construction hypotheses. -/
theorem squareMaskScore_iff_le {n s : ℕ} (hn : 0 < n) :
    SquareMaskScore n s ↔ s ≤ maxPreserved n n := by
  constructor
  · rintro ⟨F,hF,rfl⟩
    rw [maxPreserved_eq_maxForcedAcyclic hn hn]
    exact Finset.le_sup (f := Finset.card) hF
  · intro hs
    obtain ⟨T,_,hT,hscore⟩ := exists_spanningSubtree_numPreserved_eq_maxPreserved hn hn
    let F := Finset.univ.filter (fun v => isPreserved n n T v)
    have hF : F ∈ acyclicForcedSets n n := by
      apply mem_acyclicForcedSets.mpr
      apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
      intro v hv
      exact preservesIncidentEdges_of_le_of_degree_eq _ _ hT.le v
        (Finset.mem_filter.mp (show v ∈ F from hv)).2
    exact squareMaskScore_down ⟨F,hF,rfl⟩ (hs.trans_eq hscore.symm)

theorem exactSquareFormula_iff_masks : ExactSquareFormula ↔
    ∀ n, 0 < n → SquareMaskScore n (squareScore n) ∧
      ¬ SquareMaskScore n (squareScore n+1) := by
  constructor
  · intro h n hn
    rw [squareMaskScore_iff_le hn, squareMaskScore_iff_le hn, h n hn]
    omega
  · intro h n hn
    specialize h n hn
    rw [squareMaskScore_iff_le hn, squareMaskScore_iff_le hn] at h
    omega

theorem squareScore_lower_three_mul (k : ℕ) (hk : 1 ≤ k) :
    squareScore (3*k) ≤ maxPreserved (3*k) (3*k) := by
  rw [squareScore_three_mul, ← diagonalFormulaP_three_mul k hk]
  by_cases h : 7 ≤ k
  · exact matchingDiagonalConstructions_residueZero k h
  · exact matchingDiagonalConstructions_residueZeroFinite k hk (by omega)

theorem exactSquareFormula_through_five {n : ℕ} (hn : 1 ≤ n) (h : n ≤ 5) :
    maxPreserved n n = squareScore n := by
  interval_cases n
  · exact maxPreserved_one_one
  · exact maxPreserved_two_two
  · exact maxPreserved_three_three
  · exact maxPreserved_widthFour_eq_two_mul (n := 4) (by decide)
  · exact maxPreserved_five_five

theorem exactSquareFormula_seven : maxPreserved 7 7 = squareScore 7 :=
  maxPreserved_seven_seven

theorem exactSquareFormula_ten : maxPreserved 10 10 = squareScore 10 :=
  maxPreserved_ten_ten

/-- Fixed comb rows plus the marks of one accepted cap have exactly the
claimed score. This is the count; connecting transfer acceptance to the
`forcedEdgeGraph` of those rows is a separate geometric obligation. -/
theorem squareScore_comb_word (k : ℕ) (hk : 5 ≤ k) :
    ∃ w, (CombWord.run CombWord.start w).isSome ∧ w.length = 3*k+1 ∧
      2*(3*k+1)+(3*k+1-8)*(k+1)+CombWord.marks w = squareScore (3*k+1) := by
  obtain ⟨w,hw,hlen,hmarks⟩ := CombWord.exists_cap k (by omega)
  refine ⟨w,hw,hlen,?_⟩
  rw [hmarks, squareScore_three_mul_add_one k (by omega)]
  have h : 3*k+1-8+7 = 3*k := by omega
  have prod := congrArg (· * (k+1)) h
  rw [Nat.add_mul] at prod
  ring_nf at prod ⊢
  omega

end GridGraphs
