# OEIS Lookup for `P(m, n)`

This file records the result of Phase 2: searching the OEIS for the per-`m`
sequences `(P(m, n))_n` and the diagonal `(P(n, n))_n`. All matches were
verified numerically against the DP data in `data/extended.csv` and
`data/extended_long.csv`.

## Findings

| m | OEIS entry | shift / closed form | match status |
|---|------------|----------------------|--------------|
| 1 | A000027 (`n`) | `P(1, n) = n` | trivial, exact |
| 2 | (degenerate) | `P(2, n) = max(2, n)` | trivial |
| 3 | **A004772** | `P(3, n) = ⌊(4n + 2)/3⌋` for `n ≥ 3` | OEIS form `a(k) = ⌊(4k − 2)/3⌋`, our shift `k = n + 1`; verified for `n ∈ [3, 24]` |
| 4 | A005843 / A299174 (positive evens) | `P(4, n) = 2n` for `n ≥ 3` | exact match (generic sequence) |
| 5 | **A047259** | `P(5, n)` = OEIS index `n + 1` of "numbers ≡ {1,4,5} mod 6" | verified for `n ∈ [3, 24]` |
| 6 | (related to A047219) | `P(6, n) = ⌊(5n + 2)/2⌋` for `n ≥ 10` | A047219 closed form `⌊(5k − 3)/2⌋` matches under shift `k = n + 1`; verified for `n ∈ [10, 28]` |
| 7 | **A016777** | `P(7, n) = 3n + 1` for `n ≥ 7` | exact closed-form match (generic linear sequence); verified for `n ∈ [7, 30]` |
| 8 | not in OEIS | period-7 cycle `(3,3,3,3,3,3,4)` from `n = 13` | original |
| diagonal P(n,n) | not in OEIS | — | original |

The full m × n triangle (`P(m, n)` for all m, n ≤ 8) is also not in OEIS as
a single sequence.

## Cross-verification

A Python check confirms all four non-trivial closed forms (m = 3, 5, 6, 7)
agree exactly with the DP data over the entire generated range:

```
m=3 (A004772 shift): n ∈ [3, 24], 22/22 OK
m=5 (A047259 shift): n ∈ [3, 24], 22/22 OK
m=6 (A047219 shift): n ∈ [10, 28], 19/19 OK
m=7 (A016777 = 3n+1): n ∈ [7, 30], 24/24 OK
```

(Reproducible via the per-m verifier embedded in this Phase's notes; see
`Cross-check script` below.)

## Why these matches matter (and don't)

The OEIS hits for m = 3, 5, 6 are all to **simple residue sequences mod
small numbers** (`{0,2,3} mod 4`, `{1,4,5} mod 6`, `{1,3} mod 5`). This is
unsurprising structurally: the closed forms `P(m, n)` are eventually
periodic with small period `q_m`, so they trivially coincide with some
residue progression. None of the OEIS entries are about spanning trees or
grid graphs; the matches are **incidental**, in the sense that the
sequences happen to take the same values for unrelated reasons (modular
arithmetic vs. our combinatorial extremum).

In particular:

- **No OEIS entry references the full-degree spanning tree problem on
  grid graphs.** Searches for `"spanning tree" + "grid graph" + "preserved
  degree"` and `"full degree"` returned no related results.
- The closest *related* sequence is **A001353** (`a(n) = 4 a(n-1) − a(n-2)`),
  which counts the **total number of spanning trees of the 2 × n grid**
  (a different problem, exponential growth, exact closed form via
  Chebyshev). That problem's literature (Kreweras 1978, Faase 1998) deals
  with *enumeration* of spanning trees; ours deals with *optimization* over
  a per-vertex degree property.
- A more general literature exists on "grid graph spanning tree" extremal
  problems (e.g. spanning trees of maximum number of leaves), but those are
  distinct: leaf-maximization is the standard NP-hard variant; our
  full-degree-maximization is, to my present knowledge, not in OEIS-indexed
  literature.

## Implications for the roadmap

This Phase 2 result has the following effects on `docs/ROADMAP.md`:

1. **No phases are obsoleted by prior art.** The conjectures we have are
   not in any cataloged combinatorial result; the closed forms are
   genuinely new in their interpretation, even when the numeric values
   happen to match a residue progression.

2. **m = 8 and the diagonal are completely uncharted.** No OEIS entry
   corresponds. Phase 3 (motif extraction) for m = 8 was genuinely novel
   work; Phase 5 (square asymptotics) similarly has no shortcut.

3. **The OEIS matches do give us closed-form *expressions*** that we can
   target rigorously in Phase 4. For instance: any proof of `P(3, n) =
   ⌊(4n + 2)/3⌋` for `n ≥ 3` can be cross-checked against the formula
   `numbers ≡ {0, 2, 3} mod 4` (A004772), which has known generating
   function `x²(2 + x + x²) / ((1 + x + x²)(x − 1)²)`. This may streamline
   Phase 4's exposition for the m ∈ {3, 5, 6} cases.

4. **A potential paper / OEIS contribution opportunity.** Once Phase 3
   produced explicit constructions, contributing the m = 8 sequence
   `(P(8, n))_n` and the diagonal `(P(n, n))_n` to OEIS — with reference
   to this repo for the proof / DP verification — is a natural artifact.

## Search trail (for reproducibility)

The following OEIS searches were run (each via
`https://oeis.org/search?q=...`):

- m=3: `3,3,4,6,7,8,10,11,12,14,15,16,18,19,20` (no hit, drops first 3),
  `3,4,6,7,8,10,11,12,14,15,16,18,19,20` → A004772 (top hit).
- m=4: `4,4,6,8,10,12,14,16,18,20` (no hit), `4,6,8,10,12,14,16,18,20,22`
  → A005843 (generic).
- m=5: `5,5,7,10,11,13,16,17,19,22,23,25` (no hit),
  `7,10,11,13,16,17,19,22,23,25,28,29` → A047259, A144430.
- m=6: `8,12,13,16,19,21,23,26,28,31,33,36` (no hit),
  `13,16,19,21,23,26,28,31,33,36,38,41` (no hit),
  `23,26,28,31,33,36,38,41,43,46,48,51` → A047219.
- m=7: `10,14,16,19,22,25,28,31,34,37,40,43` (no hit),
  `16,19,22,25,28,31,34,37,40,43,46,49` → A016777.
- m=8: `11,16,17,21,25,27,30,34,36,40,43,46` (no hit),
  `43,46,49,52,55,58,61,65,68,71,74,77` (no hit). Original.
- diagonal: `1,2,4,8,11,16,22,27,34,42` (no hit), `2,4,8,11,16,22,27,34,42`
  (no hit), `4,8,11,16,22,27,34,42` (no hit). Original.

  Updated 2026 with extended data through n = 12: `1,2,4,8,11,16,22,27,34,42,49,58`.
  This sequence is now known to satisfy
  `P(n, n) = ⌊n²/3⌋ + n + C(n mod 3)` (Conjecture C in
  `conjectures.md`, verified at n = 4..12). A re-search with the longer
  prefix is recommended as part of any OEIS contribution.
- keyword: `spanning tree grid graph full degree` (no hit),
  `spanning tree grid graph preserved degree` → A001353 (related, but
  about *count* of spanning trees, not max preserved).

## Cross-check script

Embedded for future re-verification:

```python
# m=3
P3 = [None,3,3,4,6,7,8,10,11,12,14,15,16,18,19,20,22,23,24,26,27,28,30,31,32]
for n in range(3, len(P3)):
    assert P3[n] == (4*n + 2) // 3, f"m=3 n={n}"

# m=4
P4 = [None,4,4,6,8,10,12,14,16,18,20]  # extends as 2n for n>=3
for n in range(3, len(P4)):
    assert P4[n] == 2*n

# m=5
def A047259_at(k):
    seq = [j for j in range(1, 200) if j % 6 in (1, 4, 5)]
    return seq[k-1]
P5 = [None,5,5,7,10,11,13,16,17,19,22,23,25,28,29,31,34,35,37,40,41,43,46,47,49]
for n in range(3, len(P5)):
    assert P5[n] == A047259_at(n + 1)

# m=6
P6 = [None,6,6,8,12,13,16,19,21,23,26,28,31,33,36,38,41,43,46,48,51,53,56,58,61,63,66,68,71]
for n in range(10, len(P6)):
    assert P6[n] == (5*n + 2) // 2

# m=7
P7 = [None,7,7,10,14,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82,85,88,91]
for n in range(7, len(P7)):
    assert P7[n] == 3*n + 1
```
