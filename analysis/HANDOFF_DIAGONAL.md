# Diagonal `P(n,n)` proof — handoff (2026-04-26)

You are inheriting the diagonal proof program at the point where residue 1 is
fully constructive (`n = 3k + 1`, validated through `n = 40` by
`analysis/check_diagonal_patterns.py`) and residues 0 and 2 are at the
**skeleton stage**: parametric, dual-connected, forest-completable, but
overshooting the conjectured `q(n)` by `O(k)`.

Read `analysis/proofs_diagonal.md` end-to-end before doing anything; the
"2026-04-26 progress" section at the bottom is the primary briefing.

## TL;DR

| Residue | Pattern function | Status |
|---------|------------------|--------|
| 1 (`n = 3k+1`) | `residue_one_pattern(n)` in `diagonal_patterns.py` | exact, verified to n=40 |
| 2 (`n = 3k+2`) | `residue_two_pattern(n)` (skeleton) | n=5 exact; n>=8 has `+k` excess |
| 0 (`n = 3k`) | `residue_zero_pattern(n)` (skeleton) | n>=6 has `+(2k-3)` excess |

All three patterns are forest+dual valid for every relevant n. Only residue 1
matches the conjectured `q(n)` exactly.

## What still needs to happen

1. **Residue-2 extension patch.** The skeleton overshoots by exactly `k` for
   `n = 3k + 2`. Find the periodic `O(1)`-size patch that absorbs the `+k`
   while keeping forest+dual valid. Most likely rewrites the row-2 bridges as
   "staircase" bridges that span two cells.

2. **Residue-0 extension patch.** Analogous, with `+(2k - 3)` excess. Pattern
   is consistent with "save 2 per strip, plus 1 boundary correction" but
   needs to be made explicit.

3. **Promote `check_diagonal_patterns.py` to all three residues** once the
   patches are exact.

4. **Then** Propositions L0 and L2 in `proofs_diagonal.md` (informal proofs).

5. **Only after the construction side is settled**, tackle the matching
   upper-bound theorem (induced-edge decycling lower bound). This is parallel
   work not blocking the construction.

## Hard constraint from the user

**Do not push the empirical horizon beyond n = 15.** Cached witnesses at
n = 12, 13, 14, 15 (in `data/diagonal_u_*.txt`) are the only allowed empirical
inputs; the construction problem is now purely combinatorial. The user
explicitly said: "don't do anything empirical because i don't think there are
many algorithmic gains to be recovered anymore".

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
sweep(residue_zero_pattern, [6, 9, 12, 15])
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
| `analysis/search_residue.py` | Random/constrained local search for spot-check witnesses. |
| `analysis/diagonal_patterns.py` (rewritten) | `residue_one_pattern`, `residue_two_pattern`, `residue_zero_pattern`, plus skeleton variants and rejected experimental patterns. |

## Code map (existing)

| File | Purpose |
|------|---------|
| `analysis/check_diagonal_patterns.py` | End-to-end checker. Currently only iterates residue 1. **Extend** when residues 0/2 patterns are exact. |
| `analysis/dual_decycling.py` | Planar-dual analysis for any U-pattern on stdin. |
| `analysis/tile_symmetry.py` | Group 3x3 tiles by dihedral class. |
| `analysis/tile_class_matrix.py` | Print tile-class matrix for a witness (read from stdin). |
| `analysis/u_pattern_stats.py` | Row/strip/sliding-window U counts. |
| `analysis/crop_diff.py` | Compare residue-0/2 cached witnesses against cropped residue-1 patterns. |
| `analysis/proofs_diagonal.md` | Complete proof program; ~1100 lines; the authoritative source. |
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

The skeletons in `residue_zero_pattern` and `residue_two_pattern` are clean,
parametric, and forest-dual valid. They are the **first parametric residue-0
and residue-2 patterns recorded in this project** (the prior experimental
patterns had disconnected duals). The remaining work is to remove the small
`O(k)` excess.
