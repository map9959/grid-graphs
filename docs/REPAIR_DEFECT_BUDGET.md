# What the two incomplete-frame obstructions actually cost

At 103 the deep unrestricted chart allows `7/6` of charge at score
3647 (`19782392` at scale `16956336`). A repair error is a marked
off-pitch end site, or a missing protected site with at least one
marked guard neighbor as in the [joint frame proof](JOINT_ALIGNED_FRAME.md).
Apply the criterion separately in the horizontal and vertical frames,
**on the same marking**.

**Exact localization.** In one orientation let `G` mean that one
of the proposed bars, at columns 3 and `n-4`, has a missing site with
a marked guard neighbor between rows 9 and `n-10` inclusive. For
each near-end depth `a=1..9`, let `N_a` mean either an error on the
end word at row `a`, or a guarded hole on a side bar between `a` and
8. Define `S_b` by reflection at the far end. Avoiding *all* 81
repairs is equivalent to

```
G  or  (every N_a holds)  or  (every S_b holds).
```

Indeed the error condition for the particular `(a,b)` is exactly
`G or N_a or S_b`. If both end conjunctions fail, the two failing
depths can be used together. The transposed board must obey the same
disjunction. A single persistent hole can witness 81 failures, and
an atom must not be billed separately for each use.

**A cost for adjacent persistent defects.** Number coordinates from
NW. Suppose the bar at row 3 has a guarded hole in columns `30..36`,
and the bar at column 3 has one in rows `30..36`. Each uses the
appropriate transverse guard (offsets one and two in the normal
direction, and the four diagonals). The charge is at least **`1/3`**
in the following physical region plus its transpose, counting each
star and patch only once:

```
[0,11] × [21,45]  union  [12,37] × [29,37].
```

The connectors meet near the diagonal. An isolated flat-side test
is not sufficient: zero-charge models exist on the separated
neighborhoods. For the joined lower bound cap the integer budget at
`scale/3-1`, round charges down into 24 bins and allow either defect
anywhere in its seven-site interval. CaDiCaL exclusions passed
`drat-trim` at 103 and 112. Rooting at a different corner is not needed
when adding rotated copies: the tested domains contain no board
corner, physical column charges are D4-invariant with the arrow
directions transformed, and sheet labels can be induced by the actual
forest. The four corner-relative regions are disjoint. Fine location
labels have the same periodic coordinates after adding 18; the far
diagonal and far edge distances are already saturated throughout.
`repair_joined_coupon` checks every reference signature and its first
step. Consequently at most **three of the four corners** can exhibit
this pair at equality on `103+9t`: four would spend `4/3 > 7/6`.
This does not assert that all persistent defects lie in those intervals.

At 103 a satisfying joined-window model attains **exactly `1/3`**
when each actual star and patch is repriced with the unrounded dual.
So one such pair cannot exclude score 3647. At 112 the checked local
upper witness costs `283/762` (no exact minimum claimed there).

**Test on the complete collar.** `repair_collar103.b85` encodes a
mark bit and outgoing direction per site in the outer twelve layers.
The independent replay checks every forced edge and its orientation
and uses union-find to check acyclicity. It finds 4,368 vertices,
4,208 forced edges and 160 components. All 162 repair tests fail,
and all chart terms fully supported there cost **19,513,760**, within
the **19,782,392** budget. The collar was found by matching four
corner patches to flat side words; the price check uses the actual
assembled marking and no rounded charges. This is a *collar* forest,
not a spanning tree witness. With these same twelve layers even a
relaxation over *all* rootings and independent missing neighbor bits
already costs at least `41044604` when the touching terms are included.

**A sparse exclusion independent of the rest of the collar.** Starting
with just the first eleven layers of that marking, retain only two
20-square neighborhoods at SE and SW. To price fixed mark literals,
use their induced forced forest. In each tree all internal arrows
must point to one sink or one site with an exit to an unknown
neighbor. Compute all choices: moving the candidate root across an
edge reverses just that edge. Sum the least cost in each component
and the fixed patch costs. Drop terms whose support is incomplete
and terms fully inside the next strip to avoid double counting.
Remove a mark literal whenever this debit still holds. The resulting
29 SE literals cost at least `8478168`, and 33 SW literals at least
`10120224`, **without fixing any arrows**.

Only `1184000` remains. In the SW box test depths 9 through 13 with
one shared marking, actual arrows and this residual budget. Seven
fixed mark literals there suffice for UNSAT, independently checked
by `drat-trim`; all other strip sites are free. In total this forbids
a **69-literal two-corner signature**, not just the saved collar.
The replay prints `#`, `.`, `?` grids for the exact assignments.
The same signature in corner-relative coordinates is forbidden on
`103+18t` at the upper target. All priced atoms remain in the two
corner neighborhoods, the budget is constant, and their fine types
are unchanged (also checked at the next size).

Thus the defect requirements fit the allowance on their full collar
supports; it is their continuation into the omitted interior that
breaks this particular candidate. Other signatures and the end-error
alternatives remain open; `3646 ≤ P(103,103) ≤ 3647` is unchanged.

**Limitation for the general formula.** The `7/6` test is for the
current upper branch, not for a one-mark improvement on the comb
throughout that branch. At general `k`, put `r=(3k-13) mod 10`.
Subtracting `comb+1` from the unrestricted real sector upper gives
`(k-26+3r)/30`. Thus any fixed number of corner coupons is
asymptotically insufficient. A loss charged repeatedly along an
interface (or a stronger construction or global inequality) is needed
to close the linear gap. The logical localization and this slack
identity are in `GridGraphs/Geometry/RepairDefectBudget.lean`.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.repair_joined_coupon --deep
python3 -B -m analysis.research_program.repair_collar_replay --deep
python3 -B -m analysis.research_program.repair_corner_literals --deep --bins=32
```
