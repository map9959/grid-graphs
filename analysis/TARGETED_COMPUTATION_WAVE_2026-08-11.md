# Targeted Computation Wave, 2026-08-11

All jobs used deterministic exhaustive enumeration, a 30-minute wall-clock
limit, and a 2 GiB virtual-memory limit per process. No SAT, random search,
beam pruning, or CEGAR was used.

## Solver Trust Audit

The existing exact transition machinery passed:

- 66,064 complete patterns through `n=4`, comparing frontier acceptance with
  direct dual connectivity;
- 197,648 bidirectional cuts through `n=4`;
- 159 streamed oriented tile transition sets;
- 39,574 packet rows from 37 incoming states;
- all five `search_n17_frontier` Rust tests, including exhaustive brute-force
  agreement through `n=3` and checkpoint/resume agreement.

These checks increase confidence in the common frontier kernel. They do not
constitute an independently checkable proof of the `n=17`, `|U|<=178` UNSAT
claim.

## Stable Residue-Two Template Grammar

`compute_residue_two_stable_interval_templates.py` exhausted all 75,296
templates in its declared grammar and found no candidate valid simultaneously
at `k=7,8,9`, i.e. `n=23,26,29`.

The excluded grammar starts from the affine residue-two family, applies a
period-at-most-three row word of one contiguous assignment inside every bulk
three-column packet, and permits all 32 subsets of five fixed cap/seam toggles.
This is a complete negative only for that grammar. It rules out a broad uniform
bulk repair but not nonuniform seams, multiple packet operations, or another
interval-incidence skeleton.

## One-Hull Closure

The exact fixed-width census is closed at `n=5`:

```text
369 normalized states
10,784 transitions
2,966 certified one-hull transitions
```

At `n=8`, one-hull closure fails. The shortest independently replayed prefix is:

```text
........
UUUUUUUU
U.UUUUU.
UUU.U.UU
..UUUUU.
```

After the fifth row the exact frontier has maximum face-cut width two, classified
as `concurrent occurrence hulls`. Thus a width-independent upper language must
represent at least two simultaneous hulls; completing the one-hull transducer
cannot prove coverage.

The mixed `n=5,8,11` run reached its one-million-transition cap after 5,592
normalized states and made no broader claim.

## Occurrence-Labelled Hall Census

The immediate-local policy fails after 11 templates: two distinct occurrences
reconverge to one terminal slot.

The transported-basin policy also fails, after 21,010 templates. With two copies
of each occurrence, four debts share a basin containing only three geometric
slots. This proves that preserving provenance and broadening to the complete
transported trace still does not pay merger multiplicity. A valid policy needs
new physical resources at reconvergences, not only occurrence labels or path
slots.

## Consequences

1. Do not extend the uniform affine packet-repair grammar automatically.
2. Replace one-hull upper states by a bounded multi-hull language before any
   further closure or potential search.
3. Any decongestion theorem must include an explicit paid-merger rule assigning
   physical primal resources to reconverged excess occurrences.

## Follow-Up Structural Audit

The affine lower family does have a clean interval-incidence description.
`check_residue_two_affine_interval_skeleton.py` verifies at `k=7,8,9` that:

```text
preserved intervals = 4k
physical attachment links = 4k-1
preserved vertices = 3k^2+6k+5
```

Every interval-star is acyclic, pairwise active supports meet in at most one
vertex, the attachment graph is a tree, and a leaf-elimination order exists.
The missing construction is therefore not an acyclicity proof for the affine
skeleton; it is a different skeleton gaining exactly `k-5` vertices. The two
known exact-count pumps cannot supply it: one has an isolated dual face and a
cyclic interval quotient, while its balanced repair has a persistent closed
two-face dual component.

On the upper side, `OrderedMultiHull.lean` formalizes that laminar ordered hulls
can have arbitrary simultaneous depth. Properly nested hulls do not require a
merger or carrier collision, so neither laminarity nor collision debt justifies
a fixed two-hull language. The unrestricted physical paid-merger map remains
exactly equivalent to `W>=n+2`; a useful theorem still needs new grid-geometric
resource ownership at first reconvergence.
