import Mathlib
import GridGraphs.Defs

/-!
# Residue-1 diagonal `U` construction: definition and cardinality

For `n = 3k + 1` with `k ≥ 1` (square grid `n × n`), the `n ≡ 1 (mod 3)`
diagonal lower-bound construction (Proposition L1 in
`analysis/proofs_diagonal.md`) builds a non-full set `U` from `k` three-row
blocks plus an empty bottom row.  Vertex `(r, c)` lies in `U` exactly when:

* `r = 3t` for some `t < k` and `c = 1`             (sparse anchor row);
* `r = 3t + 1` for some `t < k` and `1 ≤ c`         (dense second row);
* `r = 3t + 2` for some `t < k − 1` and `1 ≤ c`     (dense third row of a non-final block);
* `r = 3(k − 1) + 2 = 3k − 1` and any `c`           (full final dense row).

Row `r = 3k = n − 1` is empty.

This file gives the predicate-based `Finset` definition `uResidueOne k` and
proves the cardinality identity

```
|uResidueOne k| = 6 * k^2 + k + 1
```

which equals `q(3k + 1)` (the diagonal-program closed form). Validated
empirically by `analysis/check_diagonal_patterns.py` for every
`n = 3k + 1` in `[4, 40]`.

The generic dual-connectivity-to-forest and forest-extension bridge is proved
in `GridGraphs.GridDual`. This file does not yet prove dual connectivity of the
specific residue-one construction.
-/

namespace GridGraphs

open Finset

/-! ## Membership predicate -/

/-- Predicate deciding whether vertex `(r, c)` of the `(3k+1) × (3k+1)`
grid lies in the residue-1 `U` pattern. The four disjuncts correspond to
sparse anchor rows, dense second rows, dense third rows, and the final
full row. -/
def isInUResidueOne (k : Nat) (r c : Fin (3 * k + 1)) : Prop :=
  (r.val % 3 = 0 ∧ r.val < 3 * k ∧ c.val = 1) ∨
  (r.val % 3 = 1 ∧ r.val < 3 * k ∧ 1 ≤ c.val) ∨
  (r.val % 3 = 2 ∧ r.val + 1 < 3 * k ∧ 1 ≤ c.val) ∨
  (r.val + 1 = 3 * k)

instance (k : Nat) (r c : Fin (3 * k + 1)) :
    Decidable (isInUResidueOne k r c) := by
  unfold isInUResidueOne; infer_instance

/-! ## The construction as a Finset -/

/-- The residue-1 non-full set `U` for the `(3k+1) × (3k+1)` grid. -/
def uResidueOne (k : Nat) : Finset (GridVertex (3 * k + 1) (3 * k + 1)) :=
  (Finset.univ : Finset (Fin (3 * k + 1) × Fin (3 * k + 1))).filter
    (fun p => isInUResidueOne k p.1 p.2)

/-! ## Counting columns by row predicate -/

/-- Cardinality of the column slice `{c : Fin (3k+1) | c.val = 1}`. -/
lemma card_cols_eq_one (k : Nat) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => c.val = 1)).card = 1 := by
  have h1 : (1 : Nat) < 3 * k + 1 := by omega
  have hsubset :
      (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => c.val = 1)
        = {⟨1, h1⟩} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hc; exact Fin.ext hc
    · intro hc; rw [hc]
  rw [hsubset]; simp

/-- Cardinality of the column slice `{c : Fin (3k+1) | 1 ≤ c.val}`. -/
lemma card_cols_ge_one (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => 1 ≤ c.val)).card = 3 * k := by
  -- Bijection with `Fin (3k)` via `t ↦ ⟨t.val + 1, _⟩`.
  let f : Fin (3 * k) → Fin (3 * k + 1) := fun t => ⟨t.val + 1, by have := t.isLt; omega⟩
  have hf_inj : Function.Injective f := by
    intros a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    simpa [f] using h
  have himg : (Finset.univ : Finset (Fin (3 * k))).image f
      = (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => 1 ≤ c.val) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f]
    constructor
    · rintro ⟨t, hrt⟩
      rw [← hrt]
      simp
    · intro hc
      refine ⟨⟨c.val - 1, ?_⟩, ?_⟩
      · have := c.isLt; omega
      · apply Fin.ext
        simp; omega
  rw [← himg, Finset.card_image_of_injective _ hf_inj]
  simp

/-- Cardinality of all columns. -/
lemma card_cols_all (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun _ => True)).card = 3 * k + 1 := by
  simp

/-! ## Cardinality of `uResidueOne` -/

/-- Decompose the `U`-set as the sum over rows of the number of `U`-columns
in that row. Uses `Finset.card_eq_sum_card_fiberwise` with `f = Prod.fst`. -/
lemma uResidueOne_card_sum (k : Nat) :
    (uResidueOne k).card = ∑ r : Fin (3 * k + 1),
        ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun c => isInUResidueOne k r c)).card := by
  unfold uResidueOne
  -- Apply the fiberwise cardinality lemma with f = Prod.fst onto Finset.univ.
  trans ∑ r ∈ (Finset.univ : Finset (Fin (3*k+1))),
          (((Finset.univ : Finset (Fin (3*k+1) × Fin (3*k+1))).filter
            (fun p => isInUResidueOne k p.1 p.2)).filter (fun p => p.1 = r)).card
  · exact Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := (Finset.univ : Finset (Fin (3*k+1))))
      (by intro p _; exact Finset.mem_univ _)
  -- Reduce each fiber to a column count via the bijection c ↦ (r, c).
  apply Finset.sum_congr rfl
  intro r _
  let g : Fin (3 * k + 1) → Fin (3 * k + 1) × Fin (3 * k + 1) := fun c => (r, c)
  have g_inj : Function.Injective g := fun c₁ c₂ h => (Prod.mk.inj h).2
  have hfiber :
      ((Finset.univ : Finset (Fin (3*k+1) × Fin (3*k+1))).filter
        (fun p => isInUResidueOne k p.1 p.2)).filter (fun p => p.1 = r)
      = ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun c => isInUResidueOne k r c)).image g := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, g]
    constructor
    · rintro ⟨hin, hp1⟩
      refine ⟨p.2, ?_, ?_⟩
      · rw [hp1] at hin; exact hin
      · -- (r, p.2) = p, given p.1 = r.
        show (r, p.2) = p
        rw [← hp1]
    · rintro ⟨c, hin, hpc⟩
      rw [← hpc]
      exact ⟨hin, rfl⟩
  rw [hfiber, Finset.card_image_of_injective _ g_inj]

/-- Per-row column count: `1` for sparse anchor rows, `3k` for dense rows
(both kinds), `3k + 1` for the final full row, `0` for the bottom empty row. -/
lemma row_col_count (k : Nat) (hk : 1 ≤ k) (r : Fin (3 * k + 1)) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun c => isInUResidueOne k r c)).card =
    (if r.val + 1 = 3 * k then 3 * k + 1
     else if r.val = 3 * k then 0
     else if r.val % 3 = 0 then 1
     else 3 * k) := by
  -- Case split on the four row classes.
  by_cases h1 : r.val + 1 = 3 * k
  · -- Final full row: every c is in U via the fourth disjunct.
    simp only [h1, if_true]
    have heq : ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun c => isInUResidueOne k r c))
        = (Finset.univ : Finset (Fin (3 * k + 1))) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold isInUResidueOne
      constructor
      · intro _; trivial
      · intro _; right; right; right; exact h1
    rw [heq]; simp
  · simp only [h1, if_false]
    by_cases h2 : r.val = 3 * k
    · -- Bottom empty row.
      simp only [h2, if_true]
      have heq : ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun c => isInUResidueOne k r c)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        unfold isInUResidueOne
        rintro (⟨_, hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨_, hlt, _⟩ | hfin)
        · omega
        · omega
        · omega
        · exact h1 hfin
      rw [heq]; simp
    · simp only [h2, if_false]
      have hr_lt : r.val < 3 * k := by have := r.isLt; omega
      have hr_p1_lt : r.val + 1 < 3 * k := by omega
      by_cases h3 : r.val % 3 = 0
      · -- Sparse anchor row: only c = 1 is in U.
        simp only [h3, if_true]
        have heq : ((Finset.univ : Finset (Fin (3 * k + 1))).filter
            (fun c => isInUResidueOne k r c))
            = ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => c.val = 1)) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          unfold isInUResidueOne
          constructor
          · rintro (⟨_, _, hc⟩ | ⟨hmod, _, _⟩ | ⟨hmod, _, _⟩ | hfin)
            · exact hc
            · omega
            · omega
            · exact absurd hfin h1
          · intro hc; left; exact ⟨h3, hr_lt, hc⟩
        rw [heq]; exact card_cols_eq_one k hk
      · -- Dense row (`% 3` is 1 or 2): columns 1..n-1.
        simp only [h3, if_false]
        have hmod : r.val % 3 = 1 ∨ r.val % 3 = 2 := by omega
        have heq : ((Finset.univ : Finset (Fin (3 * k + 1))).filter
            (fun c => isInUResidueOne k r c))
            = ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun c => 1 ≤ c.val)) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          unfold isInUResidueOne
          constructor
          · rintro (⟨hmod0, _, _⟩ | ⟨_, _, hc⟩ | ⟨_, _, hc⟩ | hfin)
            · exact absurd hmod0 h3
            · exact hc
            · exact hc
            · exact absurd hfin h1
          · intro hc
            rcases hmod with hm1 | hm2
            · right; left; exact ⟨hm1, hr_lt, hc⟩
            · right; right; left; exact ⟨hm2, hr_p1_lt, hc⟩
        rw [heq]; exact card_cols_ge_one k

/-! ## Counting rows of each kind -/

/-- The set of "sparse anchor rows" is in bijection with `Fin k`. -/
lemma card_rows_sparse (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun r : Fin (3 * k + 1) =>
        r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 = 0)).card = k := by
  -- Bijection f : Fin k → Fin (3k+1), t ↦ ⟨3*t, _⟩.
  let f : Fin k → Fin (3 * k + 1) := fun t => ⟨3 * t.val, by have := t.isLt; omega⟩
  have hf_inj : Function.Injective f := by
    intros a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    have h' : 3 * a.val = 3 * b.val := by simpa [f] using h
    omega
  have himg : (Finset.univ : Finset (Fin k)).image f
      = (Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 = 0) := by
    ext r
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f]
    constructor
    · rintro ⟨t, hrt⟩
      rw [← hrt]
      have ht := t.isLt
      refine ⟨?_, ?_, ?_⟩
      · show 3 * t.val + 1 ≠ 3 * k; intro h; omega
      · show 3 * t.val ≠ 3 * k; intro h; omega
      · show (3 * t.val) % 3 = 0; simp [Nat.mul_mod_right]
    · rintro ⟨h1, h2, hmod⟩
      have hrlt : r.val < 3 * k := by have := r.isLt; omega
      refine ⟨⟨r.val / 3, ?_⟩, ?_⟩
      · have hdiv : r.val = 3 * (r.val / 3) := by
          conv_lhs => rw [← Nat.div_add_mod r.val 3]
          rw [hmod]; ring
        omega
      · apply Fin.ext
        show 3 * (r.val / 3) = r.val
        conv_rhs => rw [← Nat.div_add_mod r.val 3]
        rw [hmod]; ring
  rw [← himg, Finset.card_image_of_injective _ hf_inj]
  simp

/-- The set of dense rows (rowKind = dense) has cardinality `2k - 1` for
`k ≥ 1`. Dense rows are those with `r.val + 1 ≠ 3k`, `r.val ≠ 3k`,
`r.val % 3 ≠ 0`. -/
lemma card_rows_dense (k : Nat) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun r : Fin (3 * k + 1) =>
        r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 ≠ 0)).card = 2 * k - 1 := by
  -- We count #{r : Fin (3k+1) | r.val % 3 ≠ 0 ∧ r.val + 1 ≠ 3k}
  -- (the constraint r.val ≠ 3k is implied by r.val % 3 ≠ 0 since 3k % 3 = 0).
  have hsimp_eq : ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun r : Fin (3 * k + 1) =>
        r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 ≠ 0))
      = ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r : Fin (3 * k + 1) =>
            r.val + 1 ≠ 3 * k ∧ r.val % 3 ≠ 0)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, ?_, h3⟩
      intro he
      apply h3
      rw [he]; simp [Nat.mul_mod_right]
  rw [hsimp_eq]
  -- Count via complement: #{all} - #{r.val % 3 = 0} - #{r.val + 1 = 3k}
  -- (these two are disjoint when k ≥ 1).
  have h_total :
      ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun r => r.val + 1 ≠ 3 * k ∧ r.val % 3 ≠ 0)).card
      + ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => ¬ (r.val + 1 ≠ 3 * k ∧ r.val % 3 ≠ 0))).card = 3 * k + 1 := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  -- Compute the negated filter as the disjoint union.
  have h_compl :
      ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun r => ¬ (r.val + 1 ≠ 3 * k ∧ r.val % 3 ≠ 0))).card
      = (k + 1) + 1 := by
    -- ¬ (A ∧ B) = ¬A ∨ ¬B.  ¬A = (r.val + 1 = 3k); ¬B = (r.val % 3 = 0).
    -- These are disjoint for k ≥ 1.
    have hunion :
        (Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => ¬ (r.val + 1 ≠ 3 * k ∧ r.val % 3 ≠ 0))
        = (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val + 1 = 3 * k)
          ∪ (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val % 3 = 0) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val + 1 = 3 * k))
        ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val % 3 = 0)) := by
      rw [Finset.disjoint_filter]
      intros r _ hp1 hmod
      have hreq : r.val = 3 * k - 1 := by omega
      rw [hreq] at hmod
      have hkmod : 3 * k - 1 = 3 * (k - 1) + 2 := by omega
      rw [hkmod] at hmod
      simp at hmod
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    -- Card of `r.val + 1 = 3k`: just one row (r = 3k - 1).
    have h_unique :
        ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val + 1 = 3 * k)).card = 1 := by
      have hN : (3 * k - 1 : Nat) < 3 * k + 1 := by omega
      have hsubset :
          (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val + 1 = 3 * k)
            = {⟨3 * k - 1, hN⟩} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; apply Fin.ext; show r.val = 3 * k - 1; omega
        · intro h; rw [h]; show 3 * k - 1 + 1 = 3 * k; omega
      rw [hsubset]; simp
    -- Card of `r.val % 3 = 0`: rows {0, 3, ..., 3k}, total k + 1.
    have h_mod :
        ((Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val % 3 = 0)).card = k + 1 := by
      let f : Fin (k + 1) → Fin (3 * k + 1) := fun t => ⟨3 * t.val, by have := t.isLt; omega⟩
      have hf_inj : Function.Injective f := by
        intros a b hab
        apply Fin.ext
        have h := congrArg Fin.val hab
        have h' : 3 * a.val = 3 * b.val := by simpa [f] using h
        omega
      have himg :
          (Finset.univ : Finset (Fin (k + 1))).image f
            = (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val % 3 = 0) := by
        ext r
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f]
        constructor
        · rintro ⟨t, hrt⟩
          rw [← hrt]
          show (3 * t.val) % 3 = 0; simp [Nat.mul_mod_right]
        · intro hmod
          have hrlt : r.val < 3 * k + 1 := r.isLt
          refine ⟨⟨r.val / 3, ?_⟩, ?_⟩
          · have hdiv : r.val = 3 * (r.val / 3) := by
              conv_lhs => rw [← Nat.div_add_mod r.val 3]
              rw [hmod]; ring
            omega
          · apply Fin.ext
            show 3 * (r.val / 3) = r.val
            conv_rhs => rw [← Nat.div_add_mod r.val 3]
            rw [hmod]; ring
      rw [← himg, Finset.card_image_of_injective _ hf_inj]
      simp
    rw [h_unique, h_mod]
    ring
  omega

/-- The set of "full" rows is the singleton `{3k − 1}`. -/
lemma card_rows_full (k : Nat) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun r : Fin (3 * k + 1) => r.val + 1 = 3 * k)).card = 1 := by
  have hN : (3 * k - 1 : Nat) < 3 * k + 1 := by omega
  have hsubset :
      (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val + 1 = 3 * k)
        = {⟨3 * k - 1, hN⟩} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; apply Fin.ext; show r.val = 3 * k - 1; omega
    · intro h; rw [h]; show 3 * k - 1 + 1 = 3 * k; omega
  rw [hsubset]; simp

/-- The set of "empty" rows (only the bottom row `r = 3k`). -/
lemma card_rows_empty (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 1))).filter
      (fun r : Fin (3 * k + 1) => r.val = 3 * k)).card = 1 := by
  have hN : (3 * k : Nat) < 3 * k + 1 := by omega
  have hsubset :
      (Finset.univ : Finset (Fin (3 * k + 1))).filter (fun r => r.val = 3 * k)
        = {⟨3 * k, hN⟩} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]
  rw [hsubset]; simp

/-! ## Main cardinality theorem -/

/-- The residue-1 non-full set has cardinality `6k² + k + 1` for `k ≥ 1`.

This matches the conjectured `q(3k + 1)` from the diagonal program
(`analysis/proofs_diagonal.md`) and is empirically verified by
`analysis/check_diagonal_patterns.py` for every `n = 3k + 1` in `[4, 40]`. -/
theorem uResidueOne_card (k : Nat) (hk : 1 ≤ k) :
    (uResidueOne k).card = 6 * k ^ 2 + k + 1 := by
  rw [uResidueOne_card_sum k]
  -- Replace each summand via the per-row count.
  rw [Finset.sum_congr rfl (fun r _ => row_col_count k hk r)]
  -- Repeatedly split the nested-if sum using Finset.sum_ite, leaving four
  -- sums-of-constants that equal one of: 1*1, 0, k*1, (2k-1)*(3k).
  rw [Finset.sum_ite]
  -- After first split: `(∑ r ∈ filter A1, 3k+1) + ∑ r ∈ filter ¬A1, (if A2 then 0 else ...)`.
  -- Split the second sum on its top-level `if` (`r.val = 3 * k`).
  conv_lhs =>
    rw [show ∀ s : Finset (Fin (3 * k + 1)),
            ∑ r ∈ s, (if r.val = 3 * k then (0 : Nat)
                      else if r.val % 3 = 0 then 1 else 3 * k)
            = (∑ r ∈ s.filter (fun r => r.val = 3 * k), (0 : Nat))
              + ∑ r ∈ s.filter (fun r => ¬ r.val = 3 * k),
                  (if r.val % 3 = 0 then 1 else 3 * k) from
          fun s => Finset.sum_ite ..]
  -- Split the innermost `if`.
  conv_lhs =>
    rw [show ∀ s : Finset (Fin (3 * k + 1)),
            ∑ r ∈ s, (if r.val % 3 = 0 then (1 : Nat) else 3 * k)
            = (∑ r ∈ s.filter (fun r => r.val % 3 = 0), (1 : Nat))
              + ∑ r ∈ s.filter (fun r => ¬ r.val % 3 = 0), 3 * k from
          fun s => Finset.sum_ite ..]
  -- Now we have four sums of constants over filtered subsets of
  -- (Finset.univ : Finset (Fin (3*k+1))). Reduce each to card * constant.
  simp only [Finset.sum_const, Finset.filter_filter, smul_eq_mul]
  -- Identify the five filters with our named row-counting lemmas.
  -- Filter for "full" rows: r.val + 1 = 3 * k.
  -- Filter for "empty" rows: ¬(r.val + 1 = 3 * k) ∧ r.val = 3 * k.
  -- Filter for "sparse" rows: ¬(r.val + 1 = 3 * k) ∧ ¬r.val = 3 * k ∧ r.val % 3 = 0.
  -- Filter for "dense" rows: ¬(r.val + 1 = 3 * k) ∧ ¬r.val = 3 * k ∧ ¬r.val % 3 = 0.
  -- Replace these with our card lemmas.
  rw [card_rows_full k hk]
  -- Empty row filter: ¬(r.val+1 = 3k) ∧ r.val = 3k. Coincides with {r.val = 3k}
  -- because r.val = 3k ⇒ r.val + 1 ≠ 3k.
  have hempty_eq :
      ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun r => ¬ r.val + 1 = 3 * k ∧ r.val = 3 * k))
      = ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => r.val = 3 * k)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2; exact ⟨by omega, h2⟩
  rw [hempty_eq, card_rows_empty]
  -- Sparse row filter coincides with the rows-sparse lemma's predicate.
  have hsparse_eq :
      ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun r => (¬ r.val + 1 = 3 * k ∧ ¬ r.val = 3 * k) ∧ r.val % 3 = 0))
      = ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 = 0)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [hsparse_eq, card_rows_sparse k]
  -- Dense row filter coincides with the rows-dense lemma's predicate.
  have hdense_eq :
      ((Finset.univ : Finset (Fin (3 * k + 1))).filter
        (fun r => (¬ r.val + 1 = 3 * k ∧ ¬ r.val = 3 * k) ∧ ¬ r.val % 3 = 0))
      = ((Finset.univ : Finset (Fin (3 * k + 1))).filter
          (fun r => r.val + 1 ≠ 3 * k ∧ r.val ≠ 3 * k ∧ r.val % 3 ≠ 0)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [hdense_eq, card_rows_dense k hk]
  -- Final arithmetic. With Nat subtraction (2k - 1), substitute k = k' + 1
  -- and then use `ring` for the polynomial identity.
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  -- Convert Nat.succ k' to k' + 1 throughout.
  simp only [Nat.succ_eq_add_one]
  have h_sub : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
  rw [h_sub]
  ring

/-! ## Sanity: cardinality matches the conjectured `q(3k + 1)` -/

/-- The diagonal `q`-formula from `analysis/proofs_diagonal.md`. -/
@[simp] def q (n : Nat) : Nat :=
  let k := n / 3
  match n % 3 with
  | 0 => 6 * k ^ 2 - 3 * k + 2  -- residue 0 (informal closed form)
  | 1 => 6 * k ^ 2 + k + 1      -- residue 1
  | _ => if 5 ≤ k then 6 * k ^ 2 + 5 * k + 4 else 6 * k ^ 2 + 5 * k + 3

/-- For `n = 3k + 1`, the proven cardinality of `uResidueOne k`
matches the conjectured `q(n)`. -/
theorem uResidueOne_card_eq_q (k : Nat) (hk : 1 ≤ k) :
    (uResidueOne k).card = q (3 * k + 1) := by
  rw [uResidueOne_card k hk]
  have hdiv : (3 * k + 1) / 3 = k := by
    have he : 3 * k + 1 = 1 + k * 3 := by ring
    rw [he, Nat.add_mul_div_right _ _ (by decide : 0 < 3)]
    omega
  have hmod : (3 * k + 1) % 3 = 1 := by
    have he : 3 * k + 1 = 1 + k * 3 := by ring
    rw [he, Nat.add_mul_mod_self_right]
  -- Compute q (3*k+1) = 6*k^2 + k + 1 by reducing the match.
  have hq : q (3 * k + 1) = 6 * k ^ 2 + k + 1 := by
    unfold q
    -- After unfolding, the goal contains `let k' := (3*k+1)/3; match (3*k+1)%3 with ...`
    -- Substitute the div / mod values.
    simp only [hdiv, hmod]
  exact hq.symm

end GridGraphs
