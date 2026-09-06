# Phase 4: Matching Upper Bounds via Transfer Matrices and Witness Periods

## Overview

For each fixed width `m`, the maximum-full-degree spanning-tree problem
on the `m × n` grid graph reduces to a max-mean-cycle problem on a
finite directed graph: the column-state transfer graph. Phase 4
combines two complementary tools to determine the asymptotic slope
`α_m = lim_{n → ∞} P(m, n) / n` exactly:

* **Transfer-matrix + Karp's max-mean cycle** (`src/transfer.rs`):
  enumerate every reachable canonical column state, build the weighted
  transition graph, run streaming Karp's algorithm to get the rational
  max mean. *Rigorous* but feasible only for `m ≤ 6` due to state-space
  growth.
* **Witness gain-sequence period detection** (`src/motif.rs`):
  decode an optimal spanning tree from the witness DP, compute per-column
  full-degree counts, detect periodicity. *Empirical-but-strong* method
  that scales to `m ≤ 8` (limited only by the underlying DP solver).

Where both methods apply (`m ∈ {3, 4, 5, 6}`), they agree on `α_m`,
giving cross-validated certainty.

## Column-State Transfer Graph

State at the boundary between column `c` and column `c + 1` of an
`m × n` grid:
* `labels : (1..k)^m` — canonical component labels of the column-`c`
  vertices in the partial spanning forest. Canonicalized so labels
  appear as 1, 2, ... in row order.
* `pdeg : {0, 1, 2, 3}^m` — partial degree of each column-`c` vertex
  (counting left, up, and down edges; the right edge is undecided).

A transition `s → s'` chooses, for column `c + 1`:
* `h ∈ {0, 1}^m` — whether each horizontal edge `(r, c)–(r, c + 1)` is
  present.
* `v ∈ {0, 1}^{m − 1}` — whether each vertical edge
  `(r, c + 1)–(r + 1, c + 1)` is present.

Validity:
* The combined unions of `h` and `v` (acting on the existing component
  structure of column `c` and a fresh column `c + 1`) must remain a
  forest (no cycles).
* Every column-`c` component must have at least one row with `h[r] = 1`
  (otherwise that component "dies" without joining the rest of the
  tree).

The **gain** of `s → s'` is the number of column-`c` rows whose final
tree degree `pdeg[r] + h[r]` equals their grid degree (3 if `r` is a
top/bottom border row, 4 otherwise). `α_m` is the maximum mean weight
of any cycle in this graph.

## Per-`m` Results

For each `m ∈ {3, ..., 8}` we report the transfer-graph size (where
feasible), the Karp-rigorous `α_m`, the witness-period `α_m`, and a
representative motif extracted from the optimal witness.

### m = 3

| metric | value |
|--------|------:|
| transfer states | 36 |
| transfer edges  | 419 |
| Karp `α_3` | **4 / 3** |
| witness-period `α_3` | 4 / 3 |
| period q | 3 |

Optimal column-pattern motif (from witness at n = 24):
| col | V | H | gain |
|----:|---|---|-----:|
| 3k     | 11  | 101 | 2 |
| 3k + 1 | 01  | 001 | 1 |
| 3k + 2 | 01  | 101 | 1 |

Sum 4 over 3 columns → α = 4/3 ✓.

### m = 4

| metric | value |
|--------|------:|
| transfer states | 187 |
| transfer edges  | 6 888 |
| Karp `α_4` | **2** |
| witness-period `α_4` | 2 |
| period q | 1 |

Trivial period: every interior column has the same edge pattern (e.g.
`v = 101, h = 1001`) with gain 2. The basic UB is also 2 here, so this
is tight without Phase 4 — confirmed by the transfer matrix.

### m = 5

| metric | value |
|--------|------:|
| transfer states | 1 012 |
| transfer edges  | 118 349 |
| Karp `α_5` | **2** |
| witness-period `α_5` | 2 |
| period q | 3 (alternative q = 1 also achieves α = 2) |

The optimal cycle in the transfer graph is a self-loop with gain 2 (a
two-spine column motif preserved between columns), but the witness DP
also finds a *different* period-3 cycle [1, 4, 1] of mean 2. Both are
optimal. The period-3 motif is the one used for the new explicit
construction (see `tree_m5_period3_motif` in `check_constructions.py`)
and closes the previously-open `n ≡ 1 (mod 3)` residue class.

### m = 6

| metric | value |
|--------|------:|
| transfer states | 5 689 |
| transfer edges  | 2 117 014 |
| Karp `α_6` | **5 / 2** |
| Karp wall time | ~ 40 s |
| witness-period `α_6` | 5 / 2 |
| period q | 2 |

The Karp cycle has length 4 (a doubling of the underlying period-2 mean
cycle). Witness DP at large n confirms the period-2 gain motif `[2, 3]`.

### m = 7

| metric | value |
|--------|------:|
| transfer states | 32 957 |
| transfer edges  | 39 038 566 |
| Karp `α_7` | not run (state space too large for Karp memory and time budget) |
| witness-period `α_7` | 3 |
| period q | 1 |

The basic UB already gives `α_7 ≤ 3` tightly (since `(7 + 2)/3 = 3`),
so no improvement was needed from the transfer matrix. Witness DP
confirms a constant per-column gain of 3 in the interior, achieved by
a period-1 motif (`v = 101101, h = 1001001`).

### m = 8

| metric | value |
|--------|------:|
| transfer states | not enumerated (estimated > 100 000) |
| Karp `α_8` | not run (intractable) |
| witness-period `α_8` | **22 / 7** |
| period q | 7 |

The witness gain-sequence at `n = 35` decodes cleanly to
`[3, 3, 3, 3, 3, 3, 4]` × periodic, summing to 22 over 7 columns.
`tree_m8_witness` in `check_constructions.py` encodes the explicit
period-7 motif (alternating row-reflected blocks A and B), verified
optimal at `n ∈ {20, 34, 48}`.

## Asymptotic Summary

| m | basic UB α | Phase 4 α | gap closed by Phase 4 |
|---|-----------:|----------:|:----------------------|
| 3 | 5/3 | 4/3 | ✓ closed |
| 4 | 2   | 2   | already tight |
| 5 | 7/3 | 2   | ✓ closed |
| 6 | 8/3 | 5/2 | ✓ closed |
| 7 | 3   | 3   | already tight |
| 8 | 10/3| 22/7| ✓ closed (empirically; Karp not run) |

The basic UB is asymptotically tight precisely when `m ≡ 1 (mod 3)`
(observed for `m ∈ {1, 4, 7}`); for the other residue classes
`m mod 3 ∈ {0, 2}`, Phase 4 establishes the tighter rationals listed
above.

## Construction Coverage After Phase 4

Comparing `python3 -m analysis.patterns.check_constructions` results:

| m | construction | optimal in n ≥ m regime (before / after) |
|---|--------------|:-----------------------------------------|
| 1 | trivial path | 49 / 49 |
| 2 | ladder       | 49 / 49 |
| 3 | period-3     | 48 / 48 |
| 4 | double spine | 47 / 47 |
| 5 | three-spine + period-3 hybrid | **31 / 46** → **46 / 46** |
| 6 | period-4 (n%4=0 only) | 11 / 11 (no change) |
| 7 | period-1     | 24 / 24 |
| 8 | period-7 (n ∈ {20, 34, 48}) | **— / 3** (new) |

## Open Items After Phase 4

* **m = 6, residues n mod 4 ∈ {1, 2, 3}**: the witness DP shows a
  period-4 interior motif consistent across all residues, but each
  residue class needs its own boundary patches. Encoding all four
  residues in `check_constructions.py` is mechanical but tedious.
* **m = 8, general n**: only `n ∈ {20, 34, 48}` (i.e. `n − 20 ∈ {0, 14, 28}`)
  is implemented. Other residues mod 14 (let alone mod 7) need
  per-residue boundary derivations.
* **Karp on m ∈ {7, 8}**: the streaming Karp variant fits in memory
  but is too slow at this state-space size. Howard's policy iteration
  would help; the implementation in this branch had a correctness bug
  and was reverted. A correct Howard's would likely converge in
  seconds.
* **Construction of theorem-grade matching upper bounds**: while we
  *compute* the rational `α_m` for `m ≤ 6` rigorously, the connection
  to a Lean-formalized statement remains future work (Phases 6–7).

## Reproduction

```bash
# Karp's max-mean cycle on the transfer graph (works for m ≤ 6).
cargo run --release -- alpha 3   # alpha=4/3,  cycle length 3
cargo run --release -- alpha 4   # alpha=2,    cycle length 1
cargo run --release -- alpha 5   # alpha=2,    cycle length 1 (alt: 3)
cargo run --release -- alpha 6   # alpha=5/2,  cycle length 4 (~40 s)

# Motif extraction via witness gain-sequence (works for any m the DP
# can solve, currently m ≤ 10 with default solver).
cargo run --release -- motif 8 35

# Per-column edge-pattern decoder (Python helper).
python3 -m analysis.witness_tools.extract_patterns 8 21

# Verify all constructions.
python3 -m analysis.patterns.check_constructions

# Regression tests cover the rational α_m for m ∈ {3..8}:
cargo test --release transfer:: motif::
```
