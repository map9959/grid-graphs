# Residue-2 q-construction — handoff (2026-05-10)

## TL;DR

Searching for a parametric construction of the conjectured `q(n) = 6k²+5k+3`
for `n = 3k+2` (residue 2 mod 3). After this session:

| n | status | source |
|---|--------|--------|
| 5 | EXPLICIT | `diagonal_patterns.residue_two_explicit_pattern(5)` (cached from solver) |
| 8 | EXPLICIT | cached from solver |
| 11 | EXPLICIT | cached from solver |
| 14 | EXPLICIT | cached from solver |
| ≥17 | OPEN | no parametric construction yet |

The slab-induction approach (Option A from the plan) succeeded for one
inductive step (`n=8 → n=11`) but **fails to extend** to `n=11 → n=14` and
beyond. The session ended without a working parametric construction for `n ≥ 17`.

## What was attempted this session

### Successful: explicit slab `n=8 → n=11`

`analysis/slab_construction.py::slab_extend_general(rows_old)` reproduces the
cached n=11 pattern exactly from cached n=8 by:

1. Inserting 3 rows at row positions `(n_old-2, n_old-1, n_old)`.
2. Inserting 3 cols at col positions `(n_old-3, n_old-2, n_old-1)`.
3. Applying 3 cell modifications:
   - ADD `(0, 1)` (top sparse anchor)
   - REMOVE `(1, 0)` (drop col-0 from row 1)
   - REMOVE `(n_new-1, n_new-1)` (drop bottom-right anchor)
4. Filling slab content with specific shape (hand-derived).

The cell mods encode a TOP/BOTTOM-ENVELOPE TRANSITION from n=8-style to
n=11-style. They are no-ops when the source pattern is already in n=11-style
envelope.

### Failed: slab `n=11 → n=14`

Same `slab_extend_general` applied to cached n=11 produces a candidate with:
- `|U| = 120` (1 over `q(14) = 119`)
- 2 cells with broken dual connectivity at `(7, 10), (8, 10)`.

**Why it fails**: the 3 envelope-transition mods are no-ops for n_old ≥ 11
(since the envelope already matches), so they no longer compensate for the
slab's intrinsic +1 overcount. The slab content itself adds `4*n_old + 4` =
`12*k_old + 12` cells but we need `12*k_old + 11`.

### Failed: search for slab-compatible alternative n=11

If cached n=11 isn't a valid base for the slab, maybe a different n=11
q-witness is.

* SA over n=11 swap moves (preserving |U|=72) for 552k iterations: NO swap
  improved the slab-extension fitness from cached n=11.
* SA-from-scratch in n=14 with FROZEN non-slab area (mapped from cached n=11)
  in 160k random trials: NO valid configuration found.

This strongly suggests cached n=11 + 3-row+3-col slab cannot, by itself,
produce a valid n=14 q-witness. The base or slab structure needs more
fundamental changes.

### Failed: 6-row + 6-col slab

Attempted to find n=14 as cached n=8 + 6-row+6-col slab. Best alignment
(deletion of 6 rows + 6 cols from n=14 to recover an 8x8 close to n=8) had
11 cell differences. Not clean enough to extract a slab.

### Failed: SA from scratch for n=17

`analysis/sa_residue2.py` runs simulated annealing seeded from cached n=14
extended with random slab fill. Best result for n=17:
- 196 cells valid (target 178; 18 over) after extensive search.
- 177 cells appeared valid mid-run but turned out to be a SA tracker bug
  (saved invalid intermediate). Corrected SA does not reach q(17).

## Files

### New this session

* `analysis/sa_residue2.py` — SA q-witness search with v35 / cached seeds.
* `analysis/slab_construction.py` — slab insertion (n=8→n=11 works exactly).

### Modified

* `analysis/diagonal_patterns.py` (already committed in user's
  `bd5081058d4c4ed38d538fd48a17948ddf4ea125`):
  - `_RESIDUE_TWO_EXPLICIT` dict caches optimal patterns for n ∈ {5, 8, 11, 14}.
  - `residue_two_explicit_pattern(n)` function returns these.
  - `STATUS_RESIDUE_TWO` registry updated.

* `analysis/proofs_diagonal.md`:
  - Section "2026-05-10 follow-up: residue-1 trim approach (rigid)" covers
    the v35/v44/v48 attempts and their tree-rigidity obstruction.
  - Section "2026-05-10 deep-dive: explicit slab n=8 → n=11 (works); n=11 →
    n=14 fails" covers the slab work.

## Verification

Run these to confirm the current state:

```bash
# Cached residue-2 patterns valid q-constructions
python3 -c "
import sys; sys.path.insert(0, 'analysis')
from construction_lab import run_check
from diagonal_patterns import residue_two_explicit_pattern
for n in [5, 8, 11, 14]:
    rows = residue_two_explicit_pattern(n)
    info = run_check(n, rows, verbose=True)
"

# Slab works for n=8→n=11 only
python3 analysis/slab_construction.py

# SA tool (works at small n, stalls at n>=11 from v35 seed)
python3 analysis/sa_residue2.py 11 --time 30
```

## Strategic recommendations for next session

1. **Re-derive the slab CONTENT from n=11→n=14 directly**. Currently the
   slab content is derived from n=8→n=11. The fact that it doesn't extend
   suggests the slab should depend on n_old in a way I haven't captured.
   Concretely: examine ALL valid q-witnesses at n=14 (via solver tie-break
   variation, SA, or by manually constructing) and find one that's `cached
   n=11 + clean slab`.

2. **Try slab insertion at a DIFFERENT position**. I used `(ir, ic) = (n_old-2, n_old-3)`.
   Try other positions (e.g., near the symmetry axis at `n_old/2`). The
   n=11 cached has natural symmetry about row 5; inserting AT row 5 might
   give a cleaner structure than inserting near the bottom.

3. **Larger slab (n → n+6) within mod-6 residue class**. Already tried via
   contiguous deletion: 11 differences. Try non-contiguous; or design a
   custom 6-row+6-col slab.

4. **Approach via residue 0 first**. The proofs_diagonal.md "2026-04-26
   progress" section notes residue 0 has a similar skeleton with `2k-3`
   excess. Maybe residue 0 is easier to crack and informs residue 2.

5. **Accept residue 2 needs explicit witnesses**. Cache via the solver up to
   the largest n we can compute. Document this as the construction for
   small n; pursue upper bound for large n.

6. **Look at the cached n=14 in transposed form**. The transpose of cached
   n=14 has `top empty + row 1 fully dense + (sparse, dense, dense)-like
   middle blocks`, which is closer to residue-1 structure. Maybe the slab
   extension is cleaner in transposed coordinates.

## Hard constraint reminders (from earlier handoff)

* **DO NOT push the empirical horizon beyond n=15** by running the exact
  solver. Cached witnesses at n=12, 13, 14, 15 are the only allowed
  empirical inputs.
* SA over CANDIDATE patterns at n>15 IS allowed (it's not pushing the
  exact-solver horizon; it's searching for valid q-witnesses given the
  formula's target count).

## Key files for the next agent

| File | Purpose |
|------|---------|
| `analysis/proofs_diagonal.md` | Authoritative proof program; ~1200 lines |
| `analysis/diagonal_patterns.py` | Cached residue-1 (verified to n=40) and residue-2 (n ∈ {5,8,11,14}) |
| `analysis/slab_construction.py` | Slab insertion (works for n=8→n=11 only) |
| `analysis/sa_residue2.py` | SA q-witness search tool |
| `analysis/construction_lab.py` | Verification: dual + forest + greedy completion |
| `data/diagonal_u_*.txt` | Cached fullub-pattern outputs for n ∈ {5,...,15} |

## Next concrete TODO

1. Find an alternative n=11 q-witness (via SA or constructive) that, when
   slab-extended via my current slab function, gives valid n=14.
2. OR redesign the slab content to depend on n_old's local structure.
3. OR shift to attacking residue 0 first.

The n=8→n=11 slab is a real piece of progress and a starting point. The
remaining task is to make it work for k_old ≥ 3.
