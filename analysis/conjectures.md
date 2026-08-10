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

**Status: formally proved in Lean for every `n ≥ 2`.**
`maxPreserved_widthFour_eq_two_mul` gives `P(4,n)=2n`. The lower proof uses two
acyclic forced combs; the upper proof uses checkerboard-split cotree waste and
an omitted perimeter edge.

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

## Conjecture for m = 9

P-values for `n = 9..30`: `34, 38, 41, 44, 48, 51, 55, 58, 62, 65, 69, 72,
76, 79, 83, 86, 90, ..., 107`. Differences eventually stabilize on the
period-2 cycle `(3, 4)`. Asymptotic: **`α₉ = 7/2`**.

For `n` large enough (eventually-periodic regime, n ≥ ~14):
- `n ≡ 0 (mod 2)` (even): `P(9, n) = (7n - 4)/2`
- `n ≡ 1 (mod 2)` (odd): `P(9, n) = (7n - 3)/2 - δ` for some bounded δ.

**Status: empirical for n ≤ 30; α₉ = 7/2 confirmed by witness gain-period
detection (`cargo run -- motif 9 25` → period 2, motif [4, 3]).**

This is the second m ≡ 0 (mod 3) data point after m = 6 (which had
α₆ = 5/2). Both have q = 2.

## Conjecture for m = 10

For `n ≥ 10`, P-values are `42, 46, 50, 54, 58, ..., 82` with constant
delta 4. **`α₁₀ = 4`** with period q₁₀ = 1.

The basic UB asymptote `(m + 2)/3 = 4` is **TIGHT** at m = 10 — confirming
**Conjecture A** below for the next m ≡ 1 (mod 3) value after m ∈ {1, 4, 7}.

**Status: empirically verified for n ∈ [10, 25]; α₁₀ = 4 confirmed by
witness gain-period detection (`cargo run -- motif 10 25` → period 1,
motif [4]).**

## Conjecture for m = 11 (preliminary)

P-values for n = 11..20: `49, 53, 58, 61, 66, 70, 74, 78, 82, 86`.
Deltas after the burn-in (n ≥ 15): `4, 4, 4, 4, 4` (5 consecutive).
Tentative: **α₁₁ = 4** with period q₁₁ = 1, but more data needed to
distinguish from a long-period cycle whose first apparent "+1" hasn't
appeared yet.

If `α₁₁ = 4` then m = 11 (m ≡ 2 mod 3) breaks the previous pattern of
m ≡ 2 (mod 3) widths having α = (m+1)/3 plus a small fractional offset
(α₂ = 1, α₅ = 2, α₈ = 22/7). For m=11 this would predict α near 4 = 12/3,
matching observation.

**Status: empirical, n ≤ 20; α₁₁ tentatively 4.**

## Conjecture for m = 12 (one data point)

`P(12, 12) = 58`. No further data. The n%3 fit (see "Diagonal P(n,n)"
section below) predicts P(12, 12) = 12² / 3 + 12 - 2 = 48 + 12 - 2 = 58 ✓.

## Asymptotic structure across `m`

| m | m%3 | α_m  | basicUB α (= (m+2)/3) | gap          |
|---|-----|------|-----------------------|--------------|
| 1 | 1   | 1    | 1     | 0   ← **tight** |
| 2 | 2   | 1    | 4/3   | 1/3 |
| 3 | 0   | 4/3  | 5/3   | 1/3 |
| 4 | 1   | 2    | 2     | 0   ← **tight** |
| 5 | 2   | 2    | 7/3   | 1/3 |
| 6 | 0   | 5/2  | 8/3   | 1/6 |
| 7 | 1   | 3    | 3     | 0   ← **tight** |
| 8 | 2   | 22/7 | 10/3  | 4/21 |
| 9 | 0   | 7/2  | 11/3  | 1/6 |
|10 | 1   | 4    | 4     | 0   ← **tight** (Phase 4 confirmed Conjecture A) |
|11 | 2   | 4 (tentative) | 13/3 | 1/3 (tentative) |

### Conjecture A (residue mod 3)

> The basic UB asymptote `α(m) = (m + 2) / 3` is tight (`α_m = (m+2)/3`)
> if and only if `m ≡ 1 (mod 3)`.

Verified for `m ∈ {1, 4, 7, 10}` (tight) and `m ∈ {2, 3, 5, 6, 8, 9}`
(strict gap). The m = 10 confirmation (Phase 4 / wide-m extension)
strengthens this from "3 data points each side" to "4 vs 6". Conjecture
A remains the most structural empirical regularity in the data.

### Conjecture B (period structure)

> When `m ≡ 1 (mod 3)`, the optimal-state cycle of the column transfer
> matrix has period 1 (`q_m = 1`); for `m ≡ 0, 2 (mod 3)` the period is
> non-trivial.

Verified for `m ≤ 10`: q ∈ {1, 1, 3, 1, 3, 2, 1, 7, 2, 1}. The widths
with q = 1 are exactly `m ∈ {1, 2, 4, 7, 10}` — four of which
(1, 4, 7, 10) are `≡ 1 (mod 3)`, matching Conjecture A; m = 2 is a
degenerate boundary case.

If Conjecture A holds, then `m ≡ 1 (mod 3)` is exactly the regime where
the basic deficiency-packing bound captures the true optimum, and the
optimal column construction is itself periodic with period 1
(i.e. there is a single "magic column" pattern that, repeated, yields the
asymptotic optimum). Identifying that column pattern explicitly for each
`m ≡ 1 (mod 3)` would constitute a constructive lower-bound proof
(and is the target of Phase 5 in the revised roadmap).

## Diagonal `P(n, n)` (square grids)

**Updated 2026 with extended DP data.** Computing `P(n, n)` for all
`n = 1..12` (the latter took ~9 minutes with the current solver):

| n | P(n,n) | density | Δ from prev | Δ² |
|---|-------:|--------:|-----:|----:|
| 1 |     1  | 1.0000  | —    | —   |
| 2 |     2  | 0.5000  | 1    | —   |
| 3 |     4  | 0.4444  | 2    | 1   |
| 4 |     8  | 0.5000  | 4    | 2   |
| 5 |    11  | 0.4400  | 3    | -1  |
| 6 |    16  | 0.4444  | 5    | 2   |
| 7 |    22  | 0.4490  | 6    | 1   |
| 8 |    27  | 0.4219  | 5    | -1  |
| 9 |    34  | 0.4198  | 7    | 2   |
|10 |    42  | 0.4200  | 8    | 1   |
|11 |    49  | 0.4050  | 7    | -1  |
|12 |    58  | 0.4028  | 9    | 2   |

The density column shows a **clear monotone decrease** from n ≥ 7 onward
— contradicting the earlier claim that `P(n, n) / n²` "stays at ~0.42".
The second-difference column from n = 4 onward shows the period-3 cycle
**(2, 1, -1)** repeating four times.

### Conjecture C — initial form (disproved at n = 17)

The first attempt at a diagonal closed form was

> For all `n ≥ 4`,  `P(n, n) = ⌊n²/3⌋ + n + C(n mod 3)`,
> where `C(1) = −1` and `C(0) = C(2) = −2`.

This holds for `n = 4..16` but fails at `n=17`, where the formula predicts 111
and the exact value is 110. The values through n = 12 were verified by
full spanning-tree DP. The n = 13 and n = 14 values are certified by the
forced-edge upper-bound DP (`fullub`) plus completed spanning-tree
witnesses; n = 15 is certified the same way after extending `fullub` to
width 15.

### Updated diagonal data (Phase 7a)

After fixing a subtle off-by-one in the DP's pruning code (the
comparison `val + potential ≤ best_next_val` should have been `<`,
otherwise tied-with-running-best paths get incorrectly skipped),
we extended the empirical horizon. The full diagonal sequence is now:

| n | P(n,n) | source | confidence |
|---|--------|--------|------------|
| 1..12 | 1, 2, 4, 8, 11, 16, 22, 27, 34, 42, 49, 58 | full DP | exact |
| 13 | 68 | `fullub-witness 13 13` | exact: forced-edge UB plus completed tree witness |
| 14 | 77 | `fullub-witness 14 14` | exact: forced-edge UB plus completed tree witness |
| 15 | 88 | `fullub-witness 15 15` | exact: forced-edge UB plus completed tree witness |
| 16 | 100 | exact frontier dual-connectivity DP | exact |
| 17 | 110 | exact mirror-quotiented frontier DP plus 179-U witness | exact |
| ≥ 18 | — | — | open |

The residual `r(n) := P(n, n) − ⌊n²/3⌋ − n` is then:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |10 |11 |12 |13 |14 |15 |16 |17 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| r |0 |−1|−2|−1|−2|−2|−1|−2|−2|−1|−2|−2|−1|−2|−2|−1|−3|

The strict 3-cycle (−1, −2, −2) holds for n = 4..16 and then breaks at n=17.
The exact frontier computation proves that no pattern with at most 178 U
vertices has connected dual, while a validated 179-U pattern exists. Hence
`P(17,17)=289-179=110` and `r(17)=-3`.

### Revised residue-two candidate

Current exact and constructive evidence supports

```text
P(3k+2,3k+2) = 3k²+7k+1  for 1 <= k <= 4,
P(3k+2,3k+2) = 3k²+7k    for k >= 5.
```

The second line is globally exact only at `k=5` (`n=17`). A valid 250-U
construction gives its lower-bound direction at `k=6` (`n=20`), while 249 U
has not been globally excluded. No target-count 333-U construction is known at
`k=7` (`n=23`).

### Open diagonal proof questions

The current picture is:

1. **Asymptotic density is `1/3`**: `lim P(n, n) / n² = 1/3`. This part
   of the original Conjecture C remains intact — every additional row
   of data still shrinks the density toward 1/3.

2. **The revised residue-two correction must be proved or refuted**: the exact
   `n=17` drop and matching `n=20` construction suggest a persistent one-unit
   correction, but no arbitrary-width construction or upper bound is known.

3. **The residual sequence is not exactly 3-periodic**: `r(17)=-3` is the
   first exception to the cycle observed from n=4 through n=16.

A complete revised closed form for `P(n,n)` is therefore an **open problem**.
The residue-two proof program is tracked in `docs/ROADMAP.md`; exact optimization
at larger squares is not the preferred next step.

### Why the original Conjecture C looked plausible

The 3-cycle `(−1, −2, −2)` holds for n = 4..16, each with a fixed offset
depending on `n mod 3`, but the exact n=17 result disproves its continuation.
