# Computer-Verified Constructive Lower Bounds (Phase 3)

This file documents the constructive lower-bound results for `P(m, n)`
produced in Phase 3. Each construction is given as an explicit
edge-set generator in `analysis/patterns/check_constructions.py` and is verified by
an independent Python checker that confirms (a) the edge set forms a
valid spanning tree of `G(m, n)` and (b) the count of full-degree vertices
matches the conjectured `P(m, n)` from `analysis/conjectures.md`.

The constructions are **asymptotic**: their description fits a periodic
column motif that is optimal for sufficiently large `n`. Small grids
where `n < m` follow a different combinatorial regime (boundary effects
dominate over the asymptotic motif), so we report the **n ≥ m regime**
separately and don't claim coverage of the n < m regime.

## Method

Phase 3 added a witness-recording variant of the frontier DP
(`src/witness.rs`). The CLI mode `cargo run --release -- witness M N`
emits an explicit optimal spanning tree as edges. By inspecting the
column-by-column structure of these emitted trees at large `n`, periodic
motifs were identified for several widths and re-encoded as closed-form
constructions in `check_constructions.py`.

The witness solver itself is regression-tested against `solve` (the
optimization-only DP) for all `1 ≤ m, n ≤ 6` plus a handful of larger
cases including `(7, 7), (8, 8), (3, 15), (4, 12)`; values match exactly.
The emitted edges are independently verified to be valid spanning trees
with the claimed full-degree count for `2 ≤ m, n ≤ 5`. So the witness
output is trustable as a source of optimal trees.

## Results (n ≥ m regime)

| m | construction | period | n range | optimal | notes |
|---|--------------|--------|---------|---------|-------|
| 1 | `tree_m1` (full path) | — | [2, 50] | 49/49 | trivial; only one spanning tree exists |
| 2 | `tree_m2` (top spine + rungs) | 1 | [2, 50] | 49/49 | trivial |
| 3 | `tree_m3_witness` | 3 | [3, 50] | 48/48 | tight |
| 4 | `tree_m4_double_spine` | 1 | [4, 50] | 47/47 | tight |
| 5 | `tree_m5_witness` (= three-spine) | 3 | [5, 50] | 31/46 | tight for n ≢ 1 (mod 3); off by 1 for n ≡ 1 (mod 3) |
| 6 | `tree_m6_witness` | 4 | n ≡ 0 (mod 4), [8, 48] | 11/11 | tight |
| 7 | `tree_m7_witness` | 1 | [7, 30] | 24/24 | tight |
| 8 | not implemented | 7 (conjectured) | — | — | DP-witness motif is too complex for hand transcription |

For widths where the construction is tight (m ∈ {1, 2, 3, 4, 7} fully and
m = 6 for n ≡ 0 (mod 4)), this yields a **constructive theorem** in the
n ≥ m regime: `P(m, n) ≥ (closed form)` is established by exhibiting an
explicit spanning tree achieving the count.

## The constructions, in detail

### m = 1 (trivial)

`G(1, n)` is a path; its only spanning tree contains every edge. Every
vertex has tree-degree equal to its grid-degree.

### m = 2 (ladder)

Top row spine (n − 1 edges) + every column rung (0, c)–(1, c) (n edges) =
2n − 1 = m·n − 1. Achieves `P(2, n) = n`.

### m = 3 (period-3 witness motif)

For each column `c ∈ [0, n − 1]`, with `c' = c mod 3`:

| `c'` | verticals included | horizontals (right-going) included |
|------|--------------------|---------------------------------------|
| 0 | both: (0, c)–(1, c) and (1, c)–(2, c) | rows 0 and 2 |
| 1 | (1, c)–(2, c) only | row 2 only |
| 2 | (1, c)–(2, c) only | rows 0 and 2 |

When `n ≡ 0 (mod 3)`, append the boundary edge `(0, n − 1)–(1, n − 1)`
to bring the edge count to `m·n − 1 = 3n − 1`.

Achieves `P(3, n) = ⌊(4n + 2)/3⌋` for all `n ≥ 3`.

### m = 4 (double spine)

Edges:
- top spine `(0, c)–(0, c + 1)` for `c ∈ [0, n − 2]`
- bottom spine `(3, c)–(3, c + 1)` for `c ∈ [0, n − 2]`
- top vertical `(0, c)–(1, c)` for every `c`
- bottom vertical `(2, c)–(3, c)` for every `c`
- single bridge `(1, 0)–(2, 0)`

Edge count: `4n − 1`. Achieves `P(4, n) = 2n`.

### m = 5 (three-spine)

Three horizontal spines on rows 0, 2, 4 — each fully present (n − 1 edges
per spine). Per-column verticals (0, c)–(1, c) (every column) and
(3, c)–(4, c) (every column), so rows 1 and 3 hang from rows 0 and 4
respectively. Plus column-0 bridges (1, 0)–(2, 0) and (2, 0)–(3, 0) to
attach row 2 to the rest of the tree.

Edge count: `3(n − 1) + 2n + 2 = 5n − 1`.

Full-degree vertices: row 0 (n vertices) + row 4 (n vertices) +
the corner `(2, 0)` of the row-2 spine. Total: `2n + 1`.

Status:
- For `n ≡ 0 (mod 3)` and `n ≡ 2 (mod 3)`: optimal (matches conjecture
  `P(5, n) = 2n + 1`).
- For `n ≡ 1 (mod 3)`: gives `2n + 1` but the conjectured optimum is
  `2n + 2`. The optimal witness solver achieves +1 by means of a
  structurally different motif (a "fully preserved interior column"
  cluster) that doesn't fit the three-spine ansatz cleanly. Closing this
  residue class is left as **follow-on work**.

### m = 6 (period-4 witness motif, n ≡ 0 mod 4 only)

Currently implemented for `n ∈ {8, 12, 16, ...}`. Boundary columns 0, 1,
n − 2, n − 1 use special structure; interior columns follow a period-4
pattern aligned with `c' = (c − 2) mod 4`.

Tested for `n ∈ {8, 12, ..., 48}`: 11/11 optimal in the n ≥ m regime.
Achieves `P(6, n) = ⌊5n/2⌋ + [n even]`.

Extending to other `n mod 4` residues requires per-residue boundary
adjustments; not done in this Phase.

### m = 7 (period-1 witness motif)

Per column:
- `c = 0`: full ladder (V = 111111) + every-row horizontal (H = 1111111)
- `c = 1`: no verticals (V = 000000) + horizontals at rows 0, 3, 6 (H = 1001001)
- `c ≥ 2`: V = 101101 (verticals at the (r, r + 1) rungs (0, 1), (2, 3), (3, 4), (5, 6)); horizontals at rows 0, 3, 6

Equivalently: **three horizontal spines** at rows 0, 3, 6, with each pair
of adjacent spines connected by a vertical chain of two rungs per column.

Achieves `P(7, n) = 3n + 1` for all `n ≥ 7`.

## Combined formal status (post-Phase 3)

For each width `m`, in the `n ≥ m` regime:

| m | constructive LB | Lean UB (algebraic) | gap (UB − LB) |
|---|-----------------|---------------------|----------------|
| 1 | `n` (trivial) | `n` (immediate) | 0 |
| 2 | `n` (m=2 ladder) | `n + 1` (`lowerB ≤ basicUB` algebra) | small |
| 3 | `⌊(4n + 2)/3⌋` (`tree_m3_witness`) | `≈ 5n/3` (`basicUB`) | n/3 (UB loose) |
| 4 | `2n` (`tree_m4_double_spine`) | `2n + 1` (`refinedUB_4n`) | exactly 1 |
| 5 | `2n + 1` (`tree_m5_witness`, n ≢ 1 mod 3) | `≈ 7n/3` (`basicUB`) | up to n/3 |
| 6 | `5n/2 + 1` (`tree_m6_witness`, n ≡ 0 mod 4) | `≈ 8n/3` (`basicUB`) | n/6 |
| 7 | `3n + 1` (`tree_m7_witness`) | `3n + 4` (`basicUB`) | exactly 3 |

For **m = 4 and m = 7**, the LB and basic UB asymptotic slopes match
(both exactly 2 and 3 respectively), so the asymptotic value of
`P(m, n) / n` is **rigorously pinned down**. The remaining `O(1)` gaps
require either tighter upper bounds (Phase 4: transfer matrix + Karp)
or sharper analytic UB derivations.

## Why m = 8 isn't here

The witness-DP output for m = 8 at n ≥ 21 shows a column structure with
a non-trivial period-7 macro-pattern (the conjectured period from the
Δ-sequence). The structure features a "central spike" column (V=1111101)
flanked by columns with shifted sub-patterns, and the boundary columns
on each end carry their own mirror-symmetric structure.

Hand-transcribing this into a closed-form generator is non-trivial. A
**transfer-matrix approach** (Phase 4: Karp's max-mean-cycle on the
column transition graph) would extract the optimal cycle automatically
and provide a more reliable path to encoding the m = 8 motif.

## Why m = 5 at n ≡ 1 (mod 3) is hard

The optimal witness tree at m = 5, n = 7 (where conjectured P = 16 = 2n + 2)
has the following structure:

```
row 0: *(2/2) .(1/3) .(1/3) *(3/3) .(1/3) .(1/3) *(2/2)
row 1: *(3/3) .(1/4) .(1/4) *(4/4) .(1/4) .(1/4) *(3/3)
row 2: *(3/3) .(1/4) .(1/4) *(4/4) .(1/4) .(1/4) *(3/3)
row 3: .(2/3) .(1/4) .(1/4) .(2/4) .(1/4) .(1/4) .(2/3)
row 4: *(2/2) *(3/3) *(3/3) *(3/3) *(3/3) *(3/3) *(2/2)
```

Note column c = 3 (the middle column): every vertex except row 4 has
ALL its grid edges in T. This requires the whole "middle column" to be a
preserved 4-cell cluster — a structure that doesn't periodically repeat
the same way the three-spine pattern does.

Achieving the +1 boost for `n ≡ 1 (mod 3)` would require interleaving
this "preserved column cluster" with the three-spine pattern at
appropriate periodic positions. Possible directions:

- A **period-9 motif**: 3 cycles of the standard period-3 pattern, with
  one of them replaced by the "preserved-column" variant. Edge count
  must balance.
- A **boundary trick** putting the preserved cluster near one end of the
  grid only.
- Picking up the structure exactly via Karp on the transfer-matrix graph
  (Phase 4).

## How to reproduce

From the repo root:

```bash
# Build and test the witness solver itself
cargo test --release witness

# Print one optimal tree for inspection
cargo run --release -- witness 5 21

# Verify all the constructions in this document
python3 -m analysis.patterns.check_constructions

# Re-extract motifs from the witness output (rendered as ASCII art)
python3 -m analysis.witness_tools.render_witness --probe
```

The script `analysis/searches/motif_search.py` contains additional candidate
motif-builders that were tried during development; the ones that worked
are migrated to `check_constructions.py`.
