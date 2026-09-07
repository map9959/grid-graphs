# L2: Terminal Tail Interface

Date: 2026-09-06. Coordinates are zero-based and intervals inclusive.
Write `h=3s`, `n=3s+5`, `k=s+1`.

## Outcome

**An improved rootless-output candidate, but no accumulating target pump.**
At n=14 the new forest has 76 centers, versus the notch follow-up's 75,
and its actual 43-vertex rootless component reaches `(h+1,h+1)`.
The improvement comes from clearing the entire terminal rail, shortening the
preceding rail, and inserting a separate frame-attached right cap. It does
not come from relabeling a frame fragment as rootless.

This geometry admits the paper construction below for every s>=3. Its
count is the source count, one better than the earlier uniform rootless
construction C(s), but its six-width count difference is still `12k+25`,
not `12k+26`. There is no verified repeatable six-width transition.

Ten bounded searches were run, only at n=11/14. Nine completed exhaustively.
The n=14 joint-left joined-output search hit its 100,000-node budget; its
76 is a lower bound, not a maximum. The stronger left-reaching subproblem
did finish and has maximum 75 at n=14. No general two-rail obstruction or
uniform optimality follows.

Read with [L2_TWO_RAIL_INTERFACE.md](L2_TWO_RAIL_INTERFACE.md), including
Notch Follow-Up. All three existing `analysis/searches/l2_*` modules were
read and left unchanged. The new module reuses their actual forced-graph
insertion and reconstruction routines, not their unbounded optimizer.

## Search Domain

Let Qplus be exactly the notch follow-up window. Define

```text
Qtail = Qplus union ({h} x [s+6,h+2])
Qjoint = Qtail union ({h-1} x [0,s+1])
                   union {(h,s+1),(h+1,s+1)}.
fixed = source_staircase(s) minus Q.
a=(h-3,s+2), u=(h-1,s+4), e=(h+1,s+4).
```

Qtail frees every remaining terminal center, jointly with the right contact
window already in Qplus: rows h-3 through h+2, columns h+2 through h+4.
At n=11 the extra tail is already in Qplus; at n=14 it adds `(9,9),(9,10)`.
Qjoint also frees the entire last left rail on row h-1, its left next-ring
and boundary centers, and the potential lower-left joining port. It does
not free the adjacent left-boundary rows or the bottom outer boundary.
All centers outside the specified Q retain source occupancy.

Every mode requires preserved u,e and the actual component of a to contain
**no ambient boundary vertex**, preserved or not. The fixed preceding rail
contains a; its footprint meets u at `(h-2,s+4)`, and u,e meet at `(h,s+4)`.
Thus this is a connected, nontrivial rootless output, not merely separation
from one selected frame root. Additional mandatory centers are:

| Reach | Required Lower Interval on Row h+1 |
| --- | --- |
| Joined | Only e |
| Right | [s+2,h+1] |
| Left | [s+1,s+4] |
| Both | [s+1,h+1] |

Intervals here constrain occupancy, not just port connectivity. The search
allows other centers anywhere in Q, arbitrary frame cuts within Q, and any
number of additional components. It does not require b=5 or a connected frame.

## Finite Results

Each run has a hard budget of 100,000 visited recursive nodes. Profiles are
`(f,r,c,b)`; c includes every ambient isolate. Sizes list the two nontrivial
components, output first; every other component is an individual isolate.

| n | Window | Reach | Variables | Nodes | Exhaustive | Best Profile | Tree Sizes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 11 | Tail | Joined | 34 | 763 | Yes | (47,11,7,6) | 31,85 |
| 11 | Tail | Right | 34 | 31 | Yes | (47,11,6,7) | 37,80 |
| 11 | Joint | Joined | 39 | 6894 | Yes | (47,11,7,6) | 31,85 |
| 11 | Joint | Left | 39 | 631 | Yes | (47,11,7,6) | 34,82 |
| 11 | Joint | Both | 39 | 147 | Yes | (47,11,6,7) | 40,77 |
| 14 | Tail | Joined | 42 | 7804 | Yes | (76,13,6,5) | 43,149 |
| 14 | Tail | Right | 42 | 33 | Yes | (76,13,6,5) | 43,149 |
| 14 | Joint | Joined | 48 | 100000 | **No** | (76,13,6,5) | 43,149 |
| 14 | Joint | Left | 48 | 15192 | Yes | (75,12,10,5) | 46,142 |
| 14 | Joint | Both | 48 | 279 | Yes | (75,12,10,5) | 46,142 |

The exact engine enumerates subsets in increasing coordinate order. Its
state contains the full ambient union-find partition, with distinct isolates.
For absent v it tests distinct component identities on
`{v} union (N(v) minus centers)`, retaining v itself. Cycles and boundary
attachment of a are monotone under adding centers, so rejected insertions
cannot become legal later in that branch. Cardinality pruning uses a feasible
incumbent; the old joined witness seeds it only when all required occupancy
conditions hold. A budget cutoff before an unvisited subtree sets
`exhaustive=False`. Counts above depend on this incumbent and search order.
These are reproducible finite searches, not formal exhaustive certificates.

The new reporter returns all actual coordinate blocks, including isolates,
and prints the entire output block as well as edits and sizes. Rebuilding
the complete forced graph verifies every returned incumbent independently
of insertion history. Regression replays compare all pairwise component
identities through the existing `audit_insertions`, not just the ledger.

## Explicit Candidate

The n=14 right-reaching witness differs from source exactly as follows:

```text
delete: (6,11), (9,6..11), (10,3), (11,5)
insert: (8,7), (8,11), (10,5..10), (11,3)
```

Its output contains a=(6,5), u=(8,7), e=(10,7), and the whole lower
interval `(10,5..10)`. The right cap `(8,11)` and the frame port `(12,10)`
are in the OTHER tree. On these named ports the partition is exactly
`{{a,u,e,(10,10)}, {(8,11),(12,10)}}`. There are also four separate
ambient isolates, so c=6. Inserting the cap after the other edits sees
five distinct components: four isolates and the frame tree. None is the
rootless output; the cap gains one center without consuming independence.

At n=11 a different right-reaching witness has 47 centers:

```text
delete: (3,10), (6,5..8), (7,10), (8,4)
insert: (5,6), (7,4..8)
```

It pays two boundary deletions (b=7), leaving a 37-vertex rootless output,
an 80-vertex frame tree and four isolates. This is a small exceptional
witness, not the s=2 instance of the next construction.

## Paper Geometry

The following is an unformalized proof argument from explicit supports,
not extrapolation from finite search. For s>=3, start from the source and:

1. Remove every original bottom-pocket center B,P.
2. Remove the complete last right rail `D={h} x [s+3,h+2]`.
3. Remove the preceding right endpoint `(h-3,h+2)`.
4. Insert `U={(h-1,s+4)}`, `V={h+1} x [s+2,h+1]`, and cap `X={(h-1,h+2)}`.
5. Insert pocket stars `J_t={(h+2-(t mod 2),s-2t)}` for `0<=t` and `s-2t>=3`.

After the deletions the only nontrivial components are the frame tree M
with the remaining rails, and shortened rail
`A={h-3} x [s+2,h+1]`. Their supports are disjoint. This follows from
the source rail footprints and deletion of A's sole frame spoke; the
deleted endpoint remains A's leaf, but its rightward edge is no longer forced.

V's interval-star support misses M: its top starts one column after the
last left rail's lower leaves end at s+1; its rightmost leaf is at column
h+2, before the right-frame leaves at h+3; its bottom row is h+2, before
the bottom-frame leaves at h+3. It also misses A. U meets A's support only
at `(h-2,s+4)` and V's only at `(h,s+4)`, and misses M. Each interval-star
graph is a tree. Gluing them through these two singleton intersections
makes a single tree O, with no ambient boundary vertex.

X meets M only at `(h-1,h+3)`, the right-frame leaf. It misses A and V.
Its center is Manhattan distance `2s-2>=4` from U, so their star supports
are disjoint. Thus X attaches to M, not O. This inequality fails at s=2;
the two cap/join stars would meet, consuming independence through the frame.

Each J_t meets M at exactly one vertex: `(h+3,s-2t)` for even t and
`(h,s-2t)` for odd t. Its support misses O and X. Consecutive pocket
centers have Manhattan distance three, and more distant pairs have larger
distance, so these supports are pairwise disjoint. The minimum column
three avoids an extra left-frame contact. This accounts for all forced
edges: the forced graph of a union is the union of the pieces' forced
graphs, including their inherited edges. The final graph therefore has
exactly two nontrivial trees O and the enlarged M, plus distinct isolates.

Both A and V have length 2s and support size `6s+2`; U has support size
five and the two singleton overlaps above. Hence

```text
|O| = (6s+2) + (6s+2) + 5 - 2 = 12s+7.
```

This is a genuine geometric attachment invariant: a,u,e and the lower-right
endpoint remain in O, X stays in M, and O avoids the entire ambient boundary.
It proves a family of forests on paper. It does NOT identify an embedding
of the old O into the next board or show a six-width transition preserves
an incoming/outgoing port state. No new Lean theorem is asserted.

## Count And Obstruction

The removed pocket has `ceil(s/2)` centers, D has 2s, and the preceding
endpoint costs one. U,V,X contribute `1+2s+1`, and the replacement pocket
has `floor((s-1)/2)=ceil(s/2)-1`. The net change from source is zero:

```text
f(s) = 3s^2+12s+11+ceil(s/2), s>=3,
f(s+2)-f(s) = 12s+37 = 12k+25.
```

Relative to C(s) and the notch joined witness this recovers one center,
but it is a constant improvement, not a recurring one per six-width step.
With `3f+r+c+b=n^2+4n`, the ambient right-hand-side difference is
`36s+120`; the target gain `12s+38` requires `Delta(r+c+b)=6`, while this
family has nine. The cap does not supply the missing three units of defect
reduction. The n=11 to n=14 score difference is NOT a six-width comparison.

The proposed left saving also has a concrete attachment obstruction.
For the n=14 witness attempt v=(10,4). Its non-preserved insertion ports
partition as `{{(9,4),(10,3),(11,4)}, {v}}`: three frame ports coincide.
After deleting last-left endpoint `(8,4)`, the partition becomes
`{{(9,4)}, {(10,3),(11,4)}, {v}}`. The pocket at `(11,3)` still supplies
the repeated frame pair, so insertion remains cyclic. Deleting it too
makes all four ports distinct isolates/output pieces and insertion legal,
with the output still rootless. Two deletions buy one insertion:
the resulting both-reaching witness has profile `(75,12,10,5)` and
component sizes `46,142,1,1,1,1,1,1,1,1`. At n=11 deleting `(5,3)` and
adding `(7,3)` instead extends left count-neutrally.

Precisely restricted conclusions: no 48-center joined rootless output
exists in either tested n=11 window; no 77-center joined output exists
in n=14 Qtail; no 76-center left-reaching output exists in n=14 Qjoint.
The unconstrained-reach n=14 Qjoint maximum is unresolved because of the
budget. These statements require the fixed preceding rail, mandatory u,e,
and stated occupancy windows. They do not exclude another rootless rail,
a changed joining row, different bottom boundary, other left-frame cuts,
or another interface. Neither this finite obstruction nor the paper family
establishes a uniform no-go or the requested accumulating pump.

## Verification

Only three new owned files were added: this document,
`analysis/searches/l2_terminal_tail_interface.py`, and its mirrored test
`analysis/tests/searches/test_l2_terminal_tail_interface.py`. Importing runs
no search; constructors reject s outside {2,3}. No board above n=14 was
materialized, no existing file edited, and no Lean build run.

Commands from the repository root:

```bash
python3 -m analysis.searches.l2_terminal_tail_interface
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_terminal_tail_interface \
  analysis.tests.searches.test_l2_two_rail_interface \
  analysis.tests.searches.test_l2_rail_repair_research \
  analysis.tests.searches.test_l2_propagating_interface \
  analysis.tests.test_package_layout
```

Tests exercise only explicit finite replays and one-node cutoff runs, not
the optimization table. They check exact component coverage, isolates,
boundary avoidance, required output occupancy, cap legality, the two
separate left-attachment collisions, window guards, and cutoff status.
All 23 tests in the command above passed. Unrelated concurrently added Lean
files were left untouched.
