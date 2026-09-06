import Mathlib
import GridGraphs.Core.Defs

/-!
# Algebraic bound expressions for the m × n grid preservation problem.

This file gives **purely arithmetic** definitions of the upper and lower bound
expressions described in `docs/DERIVATION.md`, plus a collection of
`sorry`-free lemmas establishing their basic properties.

The connection of these *expressions* to the operational quantity
`maxPreserved m n` (the maximum number of fully-preserved vertices over
all spanning trees of the grid) requires defining a real spanning tree
structure on `gridGraph`, computing its degree function, and proving
deficiency accounting. That work is **deferred** and is what the previous
sketch in this file claimed to do (with `sorry`); see `STATUS.md`.
-/

namespace GridGraphs

open Nat

/-! ## Bound expressions -/

/-- Total deficiency `D(m,n) = 2 (m-1)(n-1)`. Proven equal to `deficiency`
in `Defs.lean` via `D_eq_deficiency` below. -/
@[simp] def D (m n : Nat) : Nat := 2 * (m - 1) * (n - 1)

/-- Interior vertex count `I(m,n) = (m-2)(n-2)` when `m,n ≥ 3`, else 0. -/
@[simp] def I (m n : Nat) : Nat :=
  if m < 3 ∨ n < 3 then 0 else (m - 2) * (n - 2)

/-- Ceiling division by 3, computed via the standard Nat formula. -/
@[simp] def ceilDiv3 (x : Nat) : Nat := (x + 2) / 3

/-- Basic upper bound `UB₁(m,n) = m·n − ⌈D/3⌉`. -/
@[simp] def basicUB (m n : Nat) : Nat := m * n - ceilDiv3 (D m n)

/-- Refined thin-grid upper bound (DERIVATION.md §2). -/
@[simp] def refinedUB (m n : Nat) : Nat :=
  let d := D m n
  let i := I m n
  if d > 3 * i then
    m * n - i - ((d - 3 * i + 1) / 2)  -- ceil((d - 3i)/2)
  else
    m * n - ceilDiv3 d

/-- Conservative operational lower bound `LB(m,n) = m + n − 2` (for
`m, n ≥ 2`; `0` otherwise via `Nat` truncation). Achieved by the
"L-bend" double-comb construction in `DoubleComb.lean`. -/
@[simp] def lowerB (m n : Nat) : Nat := m + n - 2

/-! ## Algebraic properties of `ceilDiv3` -/

/-- `ceilDiv3 x` is the integer ceiling of `x / 3`: multiplied by 3 it is at
least `x`. -/
lemma ceilDiv3_mul_ge (x : Nat) : 3 * ceilDiv3 x ≥ x := by
  unfold ceilDiv3
  -- 3 * ((x + 2) / 3) ≥ x. Use division-with-remainder identity.
  have hmod : 3 * ((x + 2) / 3) + (x + 2) % 3 = x + 2 := Nat.div_add_mod (x+2) 3
  have hmlt : (x + 2) % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

/-- `ceilDiv3 x` is also bounded above by `x/3 + 1`, equivalently
`3 * ceilDiv3 x ≤ x + 2`. -/
lemma ceilDiv3_mul_le (x : Nat) : 3 * ceilDiv3 x ≤ x + 2 := by
  unfold ceilDiv3
  -- 3 * ((x+2)/3) + (x+2) % 3 = x + 2, hence 3 * ((x+2)/3) ≤ x + 2.
  have hmod : 3 * ((x + 2) / 3) + (x + 2) % 3 = x + 2 := Nat.div_add_mod (x+2) 3
  omega

/-- `ceilDiv3` is monotone. -/
lemma ceilDiv3_mono {x y : Nat} (h : x ≤ y) : ceilDiv3 x ≤ ceilDiv3 y := by
  unfold ceilDiv3
  exact Nat.div_le_div_right (by omega)

/-- Concrete value: `ceilDiv3 (3*k) = k`. Useful for the 4×n family. -/
lemma ceilDiv3_three_mul (k : Nat) : ceilDiv3 (3 * k) = k := by
  unfold ceilDiv3
  -- (3*k + 2) / 3 = k.
  -- Rewrite to the canonical form `2 + k*3` so that `Nat.add_mul_div_left` applies.
  have e : 3 * k + 2 = 2 + k * 3 := by ring
  rw [e]
  rw [Nat.add_mul_div_right _ _ (by decide : 0 < 3)]
  -- Goal: 2 / 3 + k = k.
  show 2 / 3 + k = k
  simp

/-! ## Bridge between `D` (Bounds) and `deficiency` (Defs) -/

/-- The bound expression `D` agrees with the operational `deficiency`
defined in `Defs.lean`. This is `deficiency_closed_form` restated. -/
lemma D_eq_deficiency (m n : Nat) : D m n = deficiency m n := by
  unfold D
  exact (deficiency_closed_form m n).symm

/-! ## Polynomial expansion of `D` for `m, n ≥ 1` -/

/-- For `m, n ≥ 1`, `D m n` admits the expansion
`2*m*n + 2 - 2*m - 2*n` in the natural numbers. -/
lemma D_expand {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    D m n + 2 * m + 2 * n = 2 * (m * n) + 2 := by
  unfold D
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨k, rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨j, rfl⟩
  -- (k+1)-1 = k, (j+1)-1 = j; left side becomes 2*k*j + 2*(k+1) + 2*(j+1).
  show 2 * k * j + 2 * (k + 1) + 2 * (j + 1) = 2 * ((k + 1) * (j + 1)) + 2
  ring

/-- Consequence: `D m n ≤ 3 * (m * n)` for all `m, n ≥ 1`. -/
lemma D_le_three_mn {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    D m n ≤ 3 * (m * n) := by
  have hexp := D_expand hm hn
  -- D + 2m + 2n = 2 mn + 2  ⇒  D = 2 mn + 2 - 2m - 2n ≤ 3 mn (always over ℕ).
  -- Need that 2 mn + 2 ≥ 2 m + 2 n + something; just use omega after expanding.
  -- Suffices: 2 mn + 2 ≤ 3 mn + 2m + 2n (i.e. 2 ≤ mn + 2m + 2n, holds since m,n ≥ 1).
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega)
  omega

/-! ## Properties of the basic upper bound -/

/-- `basicUB m n ≤ m * n`. -/
lemma basicUB_le_mn (m n : Nat) : basicUB m n ≤ m * n := by
  unfold basicUB; exact Nat.sub_le _ _

/-- For `m, n ≥ 1`, `ceilDiv3 (D m n) ≤ m * n`. -/
lemma ceilDiv3_D_le_mn {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ceilDiv3 (D m n) ≤ m * n := by
  -- 3 * ceilDiv3(D) ≤ D + 2 ≤ 3*m*n + 2  ⇒ ceilDiv3(D) ≤ m*n + (2/3) ⇒ ≤ m*n.
  have h1 : 3 * ceilDiv3 (D m n) ≤ D m n + 2 := ceilDiv3_mul_le _
  have h2 : D m n ≤ 3 * (m * n) := D_le_three_mn hm hn
  omega

/-! ## Closed forms for the 4 × n family (matching Rust regression tests) -/

/-- `D 4 n = 6 * (n - 1)`. -/
lemma D_4n (n : Nat) : D 4 n = 6 * (n - 1) := by
  show 2 * (4 - 1) * (n - 1) = 6 * (n - 1)
  norm_num

/-- `basicUB 4 n = 2 * n + 2` for `n ≥ 1`. -/
lemma basicUB_4n {n : Nat} (hn : 1 ≤ n) : basicUB 4 n = 2 * n + 2 := by
  unfold basicUB
  rw [D_4n]
  -- ceilDiv3 (6 * (n - 1)) = 2 * (n - 1).
  have hk : ceilDiv3 (6 * (n - 1)) = 2 * (n - 1) := by
    have e : 6 * (n - 1) = 3 * (2 * (n - 1)) := by ring
    rw [e, ceilDiv3_three_mul]
  rw [hk]
  -- 4 * n - 2 * (n - 1) = 2 * n + 2  (uses n ≥ 1 to validate Nat sub).
  omega

/-- `I 4 n = 2 * (n - 2)` when `n ≥ 3`. -/
lemma I_4n {n : Nat} (hn : 3 ≤ n) : I 4 n = 2 * (n - 2) := by
  unfold I
  have hcond : ¬ (4 < 3 ∨ n < 3) := by
    push Not; exact ⟨by decide, hn⟩
  -- After rewriting the if and reducing (4-2) to 2, goal closes definitionally.
  rw [if_neg hcond]

/-- `refinedUB 4 n = 2 * n + 1` for `n ≥ 3` (strictly improves `basicUB 4 n`). -/
lemma refinedUB_4n {n : Nat} (hn : 3 ≤ n) : refinedUB 4 n = 2 * n + 1 := by
  unfold refinedUB
  rw [D_4n, I_4n hn]
  -- D = 6*(n-1), I = 2*(n-2), so 3*I = 6*(n-2), and D - 3I = 6.
  have hgt : 6 * (n - 1) > 3 * (2 * (n - 2)) := by omega
  rw [if_pos hgt]
  -- ((6*(n-1)) - 3*(2*(n-2)) + 1) / 2 = (6 + 1) / 2 = 3.
  have hsub : 6 * (n - 1) - 3 * (2 * (n - 2)) = 6 := by omega
  rw [hsub]
  -- (6 + 1) / 2 = 3.
  show 4 * n - 2 * (n - 2) - (6 + 1) / 2 = 2 * n + 1
  -- Now omega closes (n ≥ 3, hence 2*(n-2) + 3 ≤ 4*n).
  have hd : (6 + 1) / 2 = 3 := by decide
  rw [hd]
  omega

/-- The basic upper bound on the 4×n family strictly exceeds the
refined bound by exactly 1 (for n ≥ 3). -/
lemma refinedUB_lt_basicUB_4n {n : Nat} (hn : 3 ≤ n) :
    refinedUB 4 n + 1 = basicUB 4 n := by
  rw [refinedUB_4n hn, basicUB_4n (by omega)]

/-! ## Sanity: lowerB does not exceed basicUB (for m, n ≥ 1) -/

/-- For `m, n ≥ 1`, `lowerB m n ≤ basicUB m n`. -/
lemma lowerB_le_basicUB {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    lowerB m n ≤ basicUB m n := by
  unfold lowerB basicUB
  -- We need m + n - 1 ≤ m*n - ceilDiv3(D).
  -- Use: ceilDiv3(D) ≤ m*n  AND  3*ceilDiv3(D) ≤ D + 2 = 2 m n + 4 - 2m - 2n
  -- Goal as integer relation: 3*(m + n - 1) + 3*ceilDiv3(D) ≤ 3*m*n.
  have hc_le_mn : ceilDiv3 (D m n) ≤ m * n := ceilDiv3_D_le_mn hm hn
  have h3c_hi : 3 * ceilDiv3 (D m n) ≤ D m n + 2 := ceilDiv3_mul_le _
  have hDexp : D m n + 2 * m + 2 * n = 2 * (m * n) + 2 := D_expand hm hn
  -- Now omega has full linear access (m*n is just a Nat atom).
  have hmn_ge : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega)
  omega

/-! ## Refined ≤ basic upper bound (for m, n ≥ 1) -/

/-- The refined upper bound is never worse (i.e. never larger) than the basic
upper bound, for `m, n ≥ 1`. (Mirrors the Rust regression
`refined_never_worse_and_valid`.) -/
lemma refinedUB_le_basicUB {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    refinedUB m n ≤ basicUB m n := by
  unfold refinedUB
  by_cases h : D m n > 3 * I m n
  · rw [if_pos h]
    -- Goal: m*n - I m n - (D m n - 3 * I m n + 1) / 2 ≤ basicUB m n.
    -- We need: I + ⌈(D - 3I)/2⌉ ≥ ⌈D/3⌉.
    -- Multiplied through: 6 I + 3 (D - 3 I + 1) ≥ 2 (D + 2),
    --   i.e. 6 I + 3 D - 9 I + 3 ≥ 2 D + 4  ⇔  D ≥ 3 I + 1, i.e. D > 3 I (our hyp).
    set d := D m n with hdd
    set i := I m n with hii
    set mn := m * n with hmn
    -- Monotonicity / size facts:
    have h_iD : i ≤ d / 3 := by
      -- From d > 3 i, certainly i ≤ d/3.
      have : 3 * i ≤ d := le_of_lt h
      omega
    have h_i_le_mn : i ≤ mn := by
      -- I ≤ m*n directly from definition.
      rw [hii, hmn]
      unfold I
      split_ifs with hcase
      · simp
      · push Not at hcase
        obtain ⟨hm3, hn3⟩ := hcase
        have hm2 : m - 2 ≤ m := Nat.sub_le _ _
        have hn2 : n - 2 ≤ n := Nat.sub_le _ _
        calc (m - 2) * (n - 2)
            ≤ m * (n - 2) := Nat.mul_le_mul_right _ hm2
          _ ≤ m * n := Nat.mul_le_mul_left _ hn2
    have hcD_le_mn : ceilDiv3 d ≤ mn := by
      rw [hdd, hmn]; exact ceilDiv3_D_le_mn hm hn
    have h3cD_hi : 3 * ceilDiv3 d ≤ d + 2 := by rw [hdd]; exact ceilDiv3_mul_le _
    have h3cD_lo : 3 * ceilDiv3 d ≥ d := by rw [hdd]; exact ceilDiv3_mul_ge _
    -- Define q and its sandwich:
    set q : Nat := (d - 3 * i + 1) / 2 with hq
    have hq_div : 2 * q + (d - 3 * i + 1) % 2 = d - 3 * i + 1 :=
      Nat.div_add_mod (d - 3 * i + 1) 2
    have hq_mod : (d - 3 * i + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    have h_3i_le_d : 3 * i ≤ d := le_of_lt h
    -- Key claim: i + q ≥ ceilDiv3(d).
    -- Argument over ℤ: 2 q ≥ d - 3 i, so 2 (i + q) ≥ d - i. And 6 ceilDiv3(d) ≤ 2 d + 4.
    -- We want 3 (i + q) ≥ 3 ceilDiv3(d), i.e. 6(i+q) ≥ 6 ceilDiv3(d).
    -- 6(i+q) ≥ 3 d - 3 i + 6 i = 3 d + 3 i ≥ 3 d + 3·0 = 3 d ≥ 6 ceilDiv3(d) − 4
    -- So 6(i+q) ≥ 6 ceilDiv3(d) - 4, which gives i+q ≥ ceilDiv3(d) - 1; need to tighten.
    -- Easier: we already know 3 ceilDiv3(d) ≤ d + 2, so ceilDiv3(d) ≤ (d+2)/3 ≤ (d+2)/3.
    -- And 2(i+q) ≥ d - 3 i  ⇒  6(i+q) ≥ 3(d - 3 i) = 3 d - 9 i, plus we add 6 i to get
    -- 6(i+q) + ... no, we already added 6 i. Try again:
    -- 6(i+q) = 6 i + 6 q ≥ 6 i + 3(d - 3 i) = 3 d - 3 i.
    -- Need 3 d - 3 i ≥ 6 ceilDiv3(d). Since 6 ceilDiv3(d) ≤ 2 d + 4, suffices
    --   3 d - 3 i ≥ 2 d + 4, i.e. d ≥ 3 i + 4. Hypothesis only gives d ≥ 3 i + 1.
    -- So omega may need a finer mod-2 case split. Provide also: q*2 mod parity:
    -- Actually with the divmod identity for d as well, omega should manage; provide it.
    have h3cD_div : 3 * ceilDiv3 d + (d + 2) % 3 = d + 2 := by
      unfold ceilDiv3
      exact Nat.div_add_mod (d + 2) 3
    have h3cD_modlt : (d + 2) % 3 < 3 := Nat.mod_lt _ (by decide)
    have key : i + q ≥ ceilDiv3 d := by omega
    -- Now LHS = mn - i - q ≤ mn - ceilDiv3 d = basicUB.
    show mn - i - q ≤ basicUB m n
    unfold basicUB
    -- After unfolding, goal: mn - i - q ≤ m * n - ceilDiv3(D m n).
    -- Substitute the atoms.
    show mn - i - q ≤ mn - ceilDiv3 d
    omega
  · rw [if_neg h]
    -- refined branch coincides with basic.
    rfl

end GridGraphs
