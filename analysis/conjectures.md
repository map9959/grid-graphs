# Closed-Form Conjectures for `P(m, n)`

This file states the closed-form formulas for `P(m, n)` extracted in
`recurrences.md` from DP data. Each row is a **conjecture** in that we have
verified it for all `n` up to the listed bound by exhaustive DP, but have not
yet proven it valid for arbitrary `n`. Phase 3 (`proofs_m345.md`) raises the
status to **lower-bound theorem (computer-assisted)** for several widths;
matching upper bounds will come from Phase 4 (transfer matrix / Karp).

Notation: `[P]` is the Iverson bracket (1 if `P` holds, 0 otherwise).

## Conjecture for m = 1

`P(1, n) = n` for all `n ≥ 1`.

**Status: trivially proven.** `G(1, n)` is a path; its only spanning tree is
itself, and every vertex retains its grid degree.

## Conjecture for m = 2

`P(2, n) = max(2, n)` for all `n ≥ 1`.

**Status: empirically verified for n ≤ 20.**

## Conjecture for m = 3

For `n ≥ 3`,
```
P(3, n) = ⌊4n / 3⌋ + [n ≡ 1 (mod 3)]
```
or equivalently in three cases:
- `n ≡ 0 (mod 3)`: `P(3, n) = 4n / 3`,
- `n ≡ 1 (mod 3)`: `P(3, n) = (4n + 2) / 3`,
- `n ≡ 2 (mod 3)`: `P(3, n) = (4n + 1) / 3`.

`P(3, 1) = 3`, `P(3, 2) = 3`. Asymptotic: `α₃ = 4/3`.

**Status: lower bound proved by explicit construction** (`tree_m3_witness`,
Phase 3): tight for all tested n ∈ [3, 50] (n ≥ m regime). The matching
upper bound (proving `P(3, n) ≤ ⌊(4n + 2)/3⌋`) is still empirical.

## Conjecture for m = 4

For `n ≥ 3`, `P(4, n) = 2n`. With `P(4, 1) = 4`, `P(4, 2) = 4`.
Asymptotic: `α₄ = 2`.

**Status: lower bound `P(4, n) ≥ 2n` proved by explicit construction**
(Phase 3, see `proofs_m345.md`). Combined with the Lean theorem
`refinedUB_4n: refinedUB(4, n) = 2n + 1`, this pins `P(4, n) ∈ {2n, 2n + 1}`
rigorously; the closed form `P(4, n) = 2n` is empirically verified for
`n ≤ 20` and matches the constructive lower bound exactly.

This is the only width in `m ≤ 8` where the *constant* term is also zero
(`α₄ · n + 0`); it is the cleanest case and the one where the basic UB α
is asymptotically tight.

## Conjecture for m = 5

For `n ≥ 4`,
```
P(5, n) = 2n + 1 + [n ≡ 1 (mod 3)]
```
i.e.
- `n ≡ 1 (mod 3)`: `P(5, n) = 2n + 2`,
- `n ≡ 0, 2 (mod 3)`: `P(5, n) = 2n + 1`.

`P(5, 1) = 5`, `P(5, 2) = 5`, `P(5, 3) = 7`. Asymptotic: `α₅ = 2`.

**Status (Phase 3):** lower bound `P(5, n) ≥ 2n + 1` proved by explicit
construction (`tree_m5_witness` in `check_constructions.py`); tight for
n ≢ 1 (mod 3). For n ≡ 1 (mod 3), the optimum is `2n + 2` (empirically),
but the three-spine construction gives only `2n + 1` — closing this
+1 residue-class gap is on the Phase 4 (Karp / transfer matrix) target
list. The matching upper bound is empirical for all residues.

## Conjecture for m = 6

For `n ≥ 10`,
```
P(6, n) = ⌊5n / 2⌋ + [n even]
```
i.e.
- `n` even: `P(6, n) = 5n/2 + 1`,
- `n` odd:  `P(6, n) = (5n + 1)/2`.

Boundary values (`n ≤ 9`) read directly from the data. Asymptotic: `α₆ = 5/2`.

**Status (Phase 3):** lower bound proved by explicit construction
(`tree_m6_witness`) for `n ≡ 0 (mod 4)` with `n ≥ 8` (the n ≥ m regime
intersected with the period-4 alignment class); tight in those cases.
Other residue classes pending Phase 4. Upper bound is empirical.

## Conjecture for m = 7

For `n ≥ 7`,
```
P(7, n) = 3n + 1
```
Boundary values (`n ≤ 6`) read directly from the data. Asymptotic: `α₇ = 3`.

**Status (Phase 3):** lower bound `P(7, n) ≥ 3n + 1` proved by explicit
construction (`tree_m7_witness`); tight for all tested n ∈ [7, 30] (n ≥ m
regime). Combined with the basic UB `3n + 4`, the asymptotic slope `α₇ = 3`
is rigorously pinned down (LB asymptotic 3 = UB asymptotic 3); only the
additive constant differs. This is the second width where the basic UB is
asymptotically tight.

## Conjecture for m = 8

For `n ≥ 13`, write `n − 13 = 7q + r` with `0 ≤ r ≤ 6`. Then
```
P(8, n) = 43 + 22q + 3r · [r ≥ 1]
```
Equivalently the period-7 difference cycle `(3, 3, 3, 3, 3, 3, 4)` repeats
with anchor `P(8, 13) = 43`. Asymptotic: `α₈ = 22/7 ≈ 3.143`.

**Status: empirically verified for `n ≤ 35`** (three full cycles).

## Asymptotic structure across `m`

| m | α_m  | basicUB α | tight? |
|---|------|-----------|--------|
| 1 | 1    | 1         | yes |
| 2 | 1    | 4/3       | no  (gap 1/3) |
| 3 | 4/3  | 5/3       | no  (gap 1/3) |
| 4 | 2    | 2         | **yes** |
| 5 | 2    | 7/3       | no  (gap 1/3) |
| 6 | 5/2  | 8/3       | no  (gap 1/6) |
| 7 | 3    | 3         | **yes** |
| 8 | 22/7 | 10/3      | no  (gap 4/21) |

### Conjecture A (residue mod 3)

> The basic UB asymptote `α(m) = (m + 2) / 3` is tight (`α_m = (m+2)/3`)
> if and only if `m ≡ 1 (mod 3)`.

Verified for `m ∈ {1, 4, 7}` (tight) and `m ∈ {2, 3, 5, 6, 8}` (strict gap).
Next test: `m = 10` (predicted tight, `α_{10} = 4`) and `m = 9` (predicted
strict gap below `11/3`).

### Conjecture B (period structure)

> When `m ≡ 1 (mod 3)`, the optimal-state cycle of the column transfer
> matrix has period 1 (`q_m = 1`); for `m ≡ 0, 2 (mod 3)` the period is
> non-trivial.

Verified for `m ≤ 8`: q ∈ {1, 1, 3, 1, 3, 2, 1, 7}. The widths with q = 1
are exactly `m ∈ {1, 2, 4, 7}` — three of which (1, 4, 7) are `≡ 1 (mod 3)`,
matching Conjecture A; m = 2 is a degenerate boundary case.

If Conjecture A holds, then `m ≡ 1 (mod 3)` is exactly the regime where
the basic deficiency-packing bound captures the true optimum, and the
optimal column construction is itself periodic with period 1
(i.e. there is a single "magic column" pattern that, repeated, yields the
asymptotic optimum). Identifying that column pattern explicitly for each
`m ≡ 1 (mod 3)` would constitute a constructive lower-bound proof.

## What this does and does not say about `P(n, n)` (square grids)

The fixed-`m` results above grow only linearly in `n`; they say **nothing
direct** about the diagonal `P(n, n)`. The basic UB gives
`P(n, n) ≤ n² / 3 + O(n)`, but neither this Phase nor the underlying DP can
yet establish a matching lower bound for square grids of growing size.
Empirically (from `data/extended.csv`), `P(n, n) / n²` is `0.421875` at
n = 8 and `0.42` at n = 10 — well above `1/3` so far, suggesting the basic UB
is not tight on the diagonal. Square asymptotics are **out of scope** for
Phases 1–4 and are handled (if at all) by Phase 5.
