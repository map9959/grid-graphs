# Diagonal `P(n,n)` proof — handoff (2026-07-23)

You are inheriting the diagonal proof program at the point where residue 1 is
fully constructive (`n = 3k + 1`, validated through `n = 40` by
`analysis/check_diagonal_patterns.py`). Residue zero now has an exact
phase-boundary family from `n=21` onward, discovered from the stochastic n=21
witness. Residue two still has a surplus skeleton and finite exact witnesses.

Read `analysis/proofs_diagonal.md` end-to-end before doing anything; the
"2026-04-26 progress" section at the bottom is the primary briefing.

## TL;DR

| Residue | Pattern function | Status |
|---------|------------------|--------|
| 1 (`n = 3k+1`) | `residue_one_pattern(n)` in `diagonal_patterns.py` | exact, verified to n=40 |
| 2 (`n = 3k+2`) | `residue_two_pattern(n)` (skeleton) | n=5 exact; n>=8 has `+k` excess |
| 0 (`n = 3k`) | cached bases plus `residue_zero_phase_pattern` | exact bases through n=21; generated exact family for every n>=21 |

Residues 1 and 0 now have exact generated infinite families. The residue-zero
phase family is computationally verified but its frontier-connectivity proof is
not yet formalized.

## What still needs to happen

1. **Residue-0 proof.** Formalize the `R_a/S_a/B_k` phase family from
   `PHASE_PATTERN.md`: the finite `B_7` frontier certificate, its extension
   transition, and the grid planar-dual implication.

2. **Residue-2 boundary cap.** Adapt the stable phase-boundary bulk to the
   residue-two cardinality and exterior-face cap.

3. **Formalize** the planar-dual implication needed by the phase proof. Forest
   extension and the preserving-tree wrapper are already in Lean.

4. **Only after the construction side is settled**, tackle the matching
   upper-bound theorem (induced-edge decycling lower bound). This is parallel
   work not blocking the construction.

## Hard constraint from the user

**Do not run the exact optimizer beyond n = 15.** Construction checks and
finite-state candidate searches above that size are allowed.

## Verification commands

```bash
# Residue 1 (still passes, do not regress).
python3 analysis/check_diagonal_patterns.py 40

# Sweep all three skeletons.
python3 -c "
import sys; sys.path.insert(0, 'analysis')
from construction_lab import sweep
from diagonal_patterns import residue_one_pattern, residue_two_pattern, residue_zero_pattern
sweep(residue_one_pattern, [4, 7, 10, 13, 16, 19, 22, 25])
sweep(residue_two_pattern, [5, 8, 11, 14])
sweep(residue_zero_pattern, [6, 9, 12, 15, 18])
"

# Inspect cached witnesses.
python3 analysis/dual_decycling.py < data/diagonal_u_14.txt
python3 analysis/tile_class_matrix.py < data/diagonal_u_14.txt
```

## Code map (new this session)

| File | Purpose |
|------|---------|
| `analysis/construction_lab.py` | Single-file pattern checker. `run_check`, `sweep`, `dual_connectivity_check`, `forest_completion_check`. The canonical way to validate any candidate. |
| `analysis/tile_alphabet.py` | Named 3x3 tile alphabet (S/C/C'/B/B'/K) with U-counts and edge signatures. |
| `analysis/tile_grammar.py` | Streamed and bidirectional dual-frontier grammar, exact cost pruning, synthesis, and verification. |
| `analysis/TILE_GRAMMAR.md` | Current grammar design, commands, and search conclusions. |
| `analysis/search_tile_production.py` | Nonlocal inserted-row/column production search and bounded rewrite experiments. |
| `analysis/search_phase_shifted_production.py` | Unaligned cell-phase width-three cross synthesis. |
| `analysis/search_frontier_caps.py` | Cost-240 diverse prefix search against exact cost-35 suffix caps. |
| `analysis/frontier_quotient.py` | Executable n=15/n=18 frontier-anchor and affine-cost checks. |
| `analysis/search_residue_anneal.py` | Exact-cardinality stochastic search with a reproducible near-hit seed and directed three-for-three repair. |
| `analysis/search_near_exchange.py` | Exhaustive local exchange and contracted corner-patch searches around the n=21 near-hit. |
| `analysis/PHASE_PATTERN.md` | Exact residue-zero family, count proof, dual-edge formulas, and connectivity induction scaffold. |
| `analysis/search_residue.py` | Random/constrained local search for spot-check witnesses. |
| `analysis/diagonal_patterns.py` (rewritten) | `residue_one_pattern`, `residue_two_pattern`, `residue_zero_pattern`, plus skeleton variants and rejected experimental patterns. |

## Code map (existing)

| File | Purpose |
|------|---------|
| `analysis/check_diagonal_patterns.py` | End-to-end checker. Now iterates residue 1 plus cached exact residue-0/2 witnesses; extend parametric dispatch when those families are complete. |
| `analysis/dual_decycling.py` | Planar-dual analysis for any U-pattern on stdin. |
| `analysis/tile_symmetry.py` | Group 3x3 tiles by dihedral class. |
| `analysis/tile_class_matrix.py` | Print tile-class matrix for a witness (read from stdin). |
| `analysis/u_pattern_stats.py` | Row/strip/sliding-window U counts. |
| `analysis/crop_diff.py` | Compare residue-0/2 cached witnesses against cropped residue-1 patterns. |
| `analysis/proofs_diagonal.md` | Complete proof program and computational findings; the authoritative source. |
| `data/diagonal_u_{12,13,14,15}.txt` | Cached `fullub-pattern` outputs. |
| `lean/GridGraphs/Forced.lean` | Forced-edge lemma (formalized). |
| `lean/GridGraphs/Diagonal.lean` | Decycling-set lemma (formalized). |

## Two key technical observations to leverage

1. **Optimal residue-0 / residue-2 dual graphs have exactly one cycle.**
   Verified in `data/diagonal_u_{12,14,15}.txt`: `dual_edges = (n-1)^2 + 1`.
   This means the construction must place exactly one "extra" U-U edge
   compared to a dual tree. The skeleton already has many extra edges; the
   patch must cancel all but one of them.

2. **The skeleton's excess is structural, not random.** Residue-2 excess `= k`
   counts the `k - 1` row-2 bridges plus one "extra anchor". Residue-0 excess
   `= 2k - 3` counts twice that minus a small constant. Both are linear in the
   number of stripe columns. The remaining work is to *replace* each bridge
   with a `O(1)`-size local pattern that contributes 1 fewer U.

## What has been ruled out

- Naive count-matching strip extensions (rejected; disconnected dual). See
  `residue_zero_experimental_pattern`, `residue_two_experimental_pattern` in
  `diagonal_patterns.py`.
- Cropping residue-1 at n+1 to n: gives n=12 cost 93 (vs target 86); not
  reducible by any local removal scheme tried.
- SA at n=12 within a 5-minute budget. SA at n=6 and n=9 finds valid but
  irregular solutions; the SA outputs do not suggest a clean parametric
  shape.
- Pure column stripes (`.UU.UU.UU.`) at n=3k: gives `6k^2`, deficit `3k - 2`.
  Maximum 2 simultaneous removals; need much more.

## What is genuinely new and useful

The skeletons remain clean parametric baselines. The more promising exact
route is now the tile grammar: horizontal streaming is checked against the row
kernel, the reflected frontier join is exhaustively checked through 3x3, and
exact residue-0 witnesses are cached at n=6,9,12,15. Exact suffix-cost pruning
cuts the n=12 wide search to 85,242 extensions. Fixing only the final tile band
of the cached n=15 class matrix finds a new exact orientation in 190,877
extensions, with an empty top row. The remaining work is to turn that stable
bottom-frontier behavior into a recurring production.

The first direct n=15→18 production search is implemented in
`analysis/search_tile_production.py`. It jointly synthesizes an inserted tile
row and column rather than fixing a crossing tile. Copied class profiles,
full-height free inserted columns, 3x3 crossing neighborhoods, arbitrary
same-cost replacements at the two cycle-closing old tiles, and the observed
n=12→15 six-position rewrite footprint all fail within the recorded beams.
Single/pair cycle-breaking scans alone cover more than 13 million transitions.
The old interior cannot remain fixed outside a small crossing patch; search
next for a multi-band state-to-state production.

That bounded search is now implemented. `tile_grammar.py` compares frontiers
across widths after deleting a three-column/face slab; n=9→12 matches after its
first two bands, but n=12→15 has no intermediate match. Exact partial-sealing
pruning and target-aware frontier-join ranking make complete-band rewrites
tractable. Freeing both preserved bands adjacent to the n=15→18 insertion was
tested across every column alignment at the central row split and across the
remaining row splits at the strongest column alignment. The best viable joins
have two components, usually one short left face interval separated from OUT.
No n=18 candidate was found. Next widen the same-cost boundary tile domain
around that explicit missing bridge while retaining the two-band state target.

That boundary widening was tested next. Both cut tiles and then the full left
tile corridor were expanded to all same-cost 3x3 patterns. The best join is
unchanged. Its only direct bridge columns are 0 and 2, but forcing either U-U
crossing eliminates the forward half-state set even with cycle allowance 2.
For column 2 this is exact after only 590 upper-half transitions. The immediate
next step is therefore to redistribute U cost among several boundary tiles,
not to widen the same-cost pattern domains or the global beam again.

That cost redistribution produced a new result. At insertion `(3,1)`, changing
only synthesized tile `(1,2)` from cost 5 to cost 6 and allowing every 6-U
pattern yields a verified n=18 witness after 20,640 transitions. The preserved
delta is +1, so the inserted cross has cost 62 rather than 63. The witness has
200 U vertices, dual `290/290`, cycle excess one, and a valid forced forest; it
is cached in `diagonal_patterns.py` and covered by `check_diagonal_patterns.py`.

A first recurrence test at n=21 found no candidate. All 49 insertion alignments
were screened at beam 50/prefix beam 100; `(4,3)` is best and leaves one isolated
cut face. The natural shifted +1 profile worsens the join, and direct bridge
columns 5 and 6 fail. Continue from this n=21 frontier target, not from the old
n=15→18 negative experiments. Do not run the exact optimizer above n=15.

The focused `(4,3)` follow-up is also complete at bounded beams. All net-0/+1
cost profiles of radius at most three in the six-tile upper corridor were
screened, as were simultaneous bridge columns `(5,6)` and `(5,8)`. Lower cut,
next-band, and bottom-cap cost changes either move the isolated component, seal
the backward half, or worsen the join. Search output now includes both side
partitions and tile provenance. Do not resume local corridor flips at this
alignment; seek a different frontier-state template or a non-insertion grammar
production for n=21.

A six-lane parallel wave has now tested those alternatives at smoke bounds.
The new unaligned cell-slab search covers 36 phase-shifted crosses and exactly
represents the known n=15→18 crop, but finds no n=21 join below four components.
Dihedral cores, the four-class boundary extrapolation, four meet cuts, and
initial wide-band replacements do not improve the existing two-component
baseline. These are bounded results, especially because scalar beam ranking
misses the known n=18 member of the phase-shifted domain.

The productive next target is explicit: an all-5 final n=21 band has 3,784
exact backward states, of which 18 project to rotated/reflected n=18 suffix
states. Search the first six bands to cost 240 with diversity retention and
per-band frontier guidance, then attach one of those exact cost-35 caps. This is
a non-insertion state production and should replace further `(4,3)` work.

Horizontal partial diversity has now been tested. Port and obligation policies
improve the cap join from 17 to 14 and 13 components, but obligation does not
improve when its partial beam doubles. A cap-seeded multicut search reaches
9 components/excess 2 at cut `4/3` and 11 components/excess 1 at `5/2` in
1,424,976 transitions; neither qualifies for promotion.

The quotient track has a decisive negative certificate for the naive key:
`O02` and `O03` project identically, while appending `O20` gives hidden cycle
excess 1 versus 3. Enrich the quotient with slab attachment/cycle ports before
attempting induction or quotient-based state merging.

## 2026-07-23 n=21 breakthrough

`search_residue_anneal.py` produced a 275-U near-hit with dual score `(1,1,0)`:
one isolated face, cycle excess one, and 400 dual edges. Exhaustive
bridge-containing two-for-two exchanges (90,804 candidates) and all exact-count
corner rewrites of sizes 4x5, 4x6, and 5x5 (7,881,200 candidates total) found no
repair. Starting from that near-hit, component-directed three-for-three moves
found independently verified exact witnesses for seeds 20, 25, and 26. The
seed-25 witness is cached as `residue_zero_explicit_pattern(21)` and passes
`check_diagonal_patterns.py 40` plus `construction_lab.run_check`: 275 U,
dual `401/401` with 401 edges, and a valid forced forest.

## 2026-07-23 phase-family breakthrough

The cached witness exposes ordinary phase rows `R_a` and one-cell-short seam
rows `S_a`. The recursive interior word
`B_(k+1) = R_(k-2) S_(k-2) B_k R_k` generates an exact residue-zero pattern for
every `k>=7`. It reproduces cached n=21 exactly and passes all construction
checks through n=120 (with a separate stress check at n=300). Cardinality is
proved algebraically: `B_k` has `2k-2` ordinary and `k-2` seam rows. The dual
edge count equals the number of dual vertices, and connectivity reduces to a
finite base/frontier transition certificate. See `PHASE_PATTERN.md`.

The first residue-two adaptation wave is negative for an unchanged phase bulk
plus fixed caps. Its useful invariant is the count decomposition
`q(3k+2) = 2n + (3k-2)(2k+1) + 1`, which cached n=11 and n=14 realize. Exact
frontier searches show that the `+1` cannot be a single promoted phase row;
the boundary defect must evolve with `k`. Continue with a stateful defect that
absorbs one or two boundary rows of the bulk, not another fixed-cap search.

That search now has reproducible artifacts. `search_residue_two_near.py` stores
three n=17 one-face near-hits and exact local/two-corner negative searches;
`search_residue_two_anneal.py` performs directed kicked repairs.
`search_residue_two_crop.py` gives a valid crossed-crop family through tested
n=41, with residual excess four at n=23. Its known local absorption classes are
closed by exhaustive searches and an edge-count certificate. The next move is
a new defect control state, not larger beams or wider versions of the same
patches.

The principal positive residue-two result is now the affine pump. Starting from
a valid 179-U n=17 base, a fixed row/column duplication produces valid patterns
for every tested `n=3k+2` through n=119 with surplus `k-4`. This uniformly
improves the old `+k` skeleton and is implemented by
`residue_two_affine_pattern`; see `AFFINE_RESIDUE2.md`. Exact conjectured-count
residue-two construction remains open.
