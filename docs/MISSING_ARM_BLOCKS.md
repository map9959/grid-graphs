# Missing-arm blocks at the equality budget

For `n=119+42t`, let `k=39+14t` and `D=198+72t`. In transposed tile
masks a column has both long arms if its word begins `6,7^12` and
ends `448^11,192`. Missing either qualifies as missing. All costs below
are tile deficits, not counts of components.

**Lower bound without a donor.** In six consecutive bulk columns the
minimum costs in the band relaxation, indexed by how many of the
middle four columns are missing, are **36,36,36,36,15** on both axes.
Take the union over arbitrary extra longitudinal steps in the bulk,
not an assumption about periodic marks. The DP inserts every forced
edge across both cuts bordering the middle four. It rejects a cycle,
a path between teeth, and a disappearing marked component that has
neither a root nor access to an exterior cut. Exact bounded cost
bitsets are closed under the homogeneous middle step. A star-phase
union in the vertical transfer gives necessary bounds for every star.

There are `k-17` such six-column windows inside tile columns `6..k-7`.
If `Q` have all four middle columns missing, summing their costs gives
`36(k-17)-21Q <= 6D`, since no tile is counted more than six times.
Thus **`Q >= max(0,ceil((72t-396)/21))`**. The windows may overlap.
At `n=623` at least 23 windows are required; this does not fix their
positions.

**Rooting restriction.** The perpendicular two-tile-deep north and
south rim transfers retain actual roots and overlap words. In the north
the six possible star offsets occur in order, with arbitrary clean
bulk length on either side of the unique isolate. In a deep column
beyond its halo to the east the north-end mask is necessarily 6; in
a deep column still ahead of the isolate (west of the halo) it is
never 6. This is a support calculation on the certified catalogues.
In a five-column block east of the halo, let 0/1 mean absence/presence
of a terminal state, indexed by the number of missing middle columns.
Allow components without a tooth to leave through the indicated outer
cuts only:

| permitted exits | 0 missing | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| none | 0 | 0 | 0 | 0 |
| west | 0 | 1 | 1 | 1 |
| east | 0 | 0 | 0 | 1 |
| both | 1 | 1 | 1 | 1 |

This check has no cost cap. In particular at least one marked component
in each such block must get its tooth from outside the block.

**Exact-budget test.** Keep strips of three to five columns. Through
both internal cuts require an actual forced connection between marks
(distance at most two); across the whole strip require a forest with
at most one tooth per component. All its columns can miss an arm while
paying any designated cost from `5H` to `6H` for width `H=3,4,5`.
The replay uses isolate distance five. At the west end take the earlier
three- and four-wide bands costing 20 and 10; at the east end take two
four-wide bands costing 10 and 22. Partition the middle `k-15` columns
into widths 3–5, assign `5H` to each, and distribute `16+2t` extra
units. This gives exactly `D`. A zero-loss repeated slice preserves the
entire labelled frontier, so the cost sets used here apply after every
14-tile enlargement. Independent physical replay checks all internal
plaquettes, marked components and both cross-cut connections. Between
different strips the assignments are not required to agree on paths;
the accepted costs are for the projection only.

**One large shared region (axis 1).** An explicit block of `H=12+8t`
columns also works, costing only `3H`. For column `x=0,...,H-1`, take
`p=1+floor(x/3)` and `M=k-2`. Its transposed word is
`6, 7^(p-1), u, 56^(M-1-p), 24, 73`, with `u=48,33,3` cyclically.
The certified words are checked across the switches and end fringes;
extra homogeneous 7 and 56 slices add only copies of the same
plaquettes. In physical coordinates each north rod ends at
longitudinal site `3p-1+(x mod 3)` in lane zero. The middle rod begins
two sites later in lane one. Distinct rods are at mark distance at least
three except for the intended joins: every middle rod ends two sites
before a single transverse marked path shared across the **entire**
block. Thus the north rods attach separately to their teeth. The
middle rods form one tree with that transverse path and no tooth,
exposed at both outer cuts. This matches the independent graph
traversal; the southern mask is 73 everywhere, so the southern arm
is missing. The west and east bands pay the rest of the exact budget
(`fan_budget`); these exterior cuts remain open.

`missing_arm_contacts` carries this unresolved tree as a distinct
virtual vertex beside the perimeter root. A new forced edge to a
previously exposed site is inserted into its actual class. A complete
one-column attachment on either side can leave the tree unresolved,
but cannot supply its root without a cycle or another sealed component.
Here “complete” requires no marked component disjoint from **both**
virtual vertices. To close via independent one-column caps exactly
one would have to connect those vertices. The finite test closes the
7 and 56 runs under arbitrary extra steps; it does not exclude a
connection requiring more columns.
The [joint transfer and periodic-cut bound](MISSING_ARM_JOINT_TRANSFER.md)
test wider attachments, exclude the full fan at every length, and
bound the deficit for any transverse period width.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.missing_arm_budget_audit
python3 -B -m analysis.research_program.missing_arm_contacts
```
