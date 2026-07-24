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

A 2026-07-19 continuation tested broader bounded-rewrite and band-pumping
families. Those also failed; details are below.

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
- 2 disconnected dual faces at `(7, 10), (8, 10)`.

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

### 2026-07-19: failed bounded-rewrite and band-pumping follow-up

New deterministic alignment diagnostics in `analysis/slab_alignment.py` show:

* The exact cached `n=8 → n=11` alignment needs only 3 copied-cell rewrites.
* The best cached `n=11 → n=14` alignment over every insertion position needs
  22 copied-cell rewrites and reaches 5 layers from the seam.
* Transposition only swaps the row/column result; it does not improve it.

`analysis/search_slab_rewrite.py` adds fixed-cardinality annealing with graded
penalties for disconnected dual faces and forced cycles. Starting from the
hand slab, searches with slab-only, halos of widths 1--4, and unrestricted
cells did not improve past `(2 disconnected faces, 2 forced cycles)`. This is
negative search evidence, not an impossibility proof.

`analysis/search_band_pump.py` tests a more structural extension: insert copies
of three contiguous old rows and columns. It found no valid exact-count pump
for `n=8 → 11`, `n=11 → 14`, or `n=14 → 17`. For `n=14 → 17`, an exhaustive
generalization allowed every insertion position, every contiguous source band,
and every possible independent 3x3 intersection. None of 1,853,550 exact-count
candidates was valid.

The hand slab on cached n=14 is not a useful second state: at n=17 it has 179
U cells against target 178 and connects only 27 of 257 dual vertices.

## Files

### New this session

* `analysis/sa_residue2.py` — SA q-witness search with v35 / cached seeds.
* `analysis/slab_construction.py` — slab insertion (n=8→n=11 works exactly).

### New in the 2026-07-19 continuation

* `analysis/slab_alignment.py` — exhaustive cached-witness slab alignment.
* `analysis/search_slab_rewrite.py` — graded fixed-count seam rewrite search.
* `analysis/search_band_pump.py` — exhaustive contiguous-band pump search.

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

1. Stop extending the fixed copied-old-structure slab family; the new searches
   give strong evidence that its interface is too restrictive.
2. Build a finite-state 3x3 grammar whose state records boundary U masks, dual
   connectivity partitions, U cost, and dual cycle excess. It must permit a
   bounded rewrite of the preceding tile band.
3. Develop the grammar on residue 0 first if residue 2 does not expose a small
   state set; the residue-0 tile layout is cleaner.

### 2026-07-19: finite-state grammar implemented

`analysis/tile_grammar.py` now implements the pivot above. Its row transition
tracks the exposed dual-face connectivity partition, previous U mask, U cost,
and dual cycle excess; three row transitions form a tile-band production.

Validation and initial synthesis results:

* Exhaustive agreement with `construction_lab.dual_connectivity_check` on all
  66,064 patterns through 4x4, including independent cycle-excess checks.
* The 24 oriented variants of `tile_alphabet.py` produce exact residue-0
  witnesses at n=6, n=9, n=12, and n=15. All pass `run_check` including forced
  acyclicity; n=12 has the expected single dual cycle.
* The n=12 witness was found after implementing exact horizontal streaming and
  widening boundary roles to geometrically compatible tile orientations.

Horizontal streaming is now implemented and checked against the original row
transition for all oriented two-tile bands at every reachable 6x6 incoming
state. The remaining bottleneck is the tail production rule. A free crossing
tile does not pump grammar n=12 to n=15 or cached n=15 to n=18. For n=15→18,
all 900 row/column pumps with exact-cost 2x2 crossing rewrites were also tested
(1,514 cost assignments; 1,875,209 streamed transitions) without success.
The tail must rewrite a larger tile region or use a different finite-state
production. See `analysis/TILE_GRAMMAR.md`.

Exact suffix-cost pruning and a reflected bottom-up frontier search are also
implemented. The frontier merge was exhaustively checked at all 1,040 cuts
through 3x3, including cycle excess. The old wide-boundary n=15 search remains
too broad and its roles exclude the cached n=15 witness. Restricting only the
bottom band to the cached orientation while allowing every upper tile to vary
within its dihedral class finds a new exact n=15 witness after 190,877
extensions. Its top row is empty. This points toward a production preserving
the bottom frontier transition rather than fixed geometric boundary roles.

`analysis/search_tile_production.py` now tests that conclusion at n=15→18.
It synthesizes a complete inserted tile row and column under the exact +63
budget. All 180 cost-compatible copied class profiles at every insertion
alignment fail for both available n=15 orientations. Freeing the full inserted
column yields one state per side centrally, but both already contain a cycle
and their join has excess four. More than 13 million additional beam-200
transitions found no cycle-free half after arbitrary same-cost 3x3 replacement
of any single preserved tile or the tested pairs around both cycle-closing
positions. The best n=12→15 six-position class-rewrite footprint also fails
when transferred and continued downward. Do not resume small crossing patches;
the next grammar production must regenerate a larger multi-band region.

Complete-band rewriting is now available with exact horizontal-prefix sealing
pruning and a backward beam ranked against the actual forward frontier. The
n=9→12 witnesses share projected frontier states after their first two bands,
but n=12→15 does not. At n=15→18, freeing both bands adjacent to the inserted
band across all central column alignments still leaves at least two joined
components in the recorded beams. The best obstruction is localized: a short
left cut-face interval remains disconnected from OUT. Widen the boundary
pattern domain around that bridge rather than returning to crossing-only
patches or immediately increasing the global beam.

The suggested bridge search has now been run. Arbitrary same-cost patterns in
the two cut tiles, neighboring boundary tiles, and the complete left corridor
do not improve the two-component join. Forcing either possible direct crossing
at columns 0 or 2 destroys all forward half states, including with one extra
cycle allowed. A future boundary-cap search must permit a multi-tile U-cost
redistribution rather than preserving every old tile's cost.

Allowing that redistribution succeeds at n=18. With insertion `(3,1)`, a
single preserved synthesized tile `(1,2)` changes from 5 U to 6 U while the
inserted cross drops from cost 63 to 62. The grammar finds a 200-U witness with
connected dual, cycle excess one, and valid forced forest in 20,640 transitions.
It is cached as an explicit residue-0 regression. A bounded n=18→21 scan has not
yet found a recurrence; its best `(4,3)` alignment leaves one isolated cut face.

A focused search around that face has now exhausted every net-0/+1 cost profile
of radius at most three in the six adjacent upper tiles, plus paired bridge and
lower-side cost variants at the recorded beams. None improves to a connected
join. This rules out the current local corridor strategy as the immediate
residue-0 recurrence candidate; the n=18 witness remains valid and cached.

Parallel nonlocal searches now include unaligned cell-phase crosses, all
dihedral source cores, stable boundary-class domains, variable meet cuts, and
wide 2→3/3→4 band replacements. None finds n=21 at the recorded smoke bounds.
The positive result is a finite set of 18 exact n=18-derived suffix targets for
an n=21 all-5 final band. Residue-0 work should next target their cost-240
incoming states with a diverse state search; residue-2 cap adaptation remains
premature until that bulk transition exists.

The exact cap-target driver now reproduces all 3,784 suffix states and 18
n=18-derived targets, but its first diverse smoke search ends at 17 components.
The independent quotient-anchor verifier succeeds. This strengthens the
state-production framework without yet supplying the residue-0 bulk transition
needed before a residue-2 cap theorem can be attempted.

Partial-state diversity and cap-seeded multicut searches improve n=21 frontier
coverage but remain at 9 or more components. The naive cross-width quotient is
also disproved as a congruence by an exhaustive one-band hidden-cycle
counterexample. Residue-2 work remains blocked on an enriched, certified bulk
state rather than on cap enumeration.

The n=8→n=11 slab is a real piece of progress and a starting point. The
remaining task is to make it work for k_old ≥ 3.

The finite residue-zero n=21 target is resolved by exact-cardinality stochastic
search, and its phase rows now give a repeatable exact family for every
`n=3k>=21`; see `PHASE_PATTERN.md`. Residue 2 remains open because adapting the
phase boundary to its different cap and cardinality correction has not yet been
done.
