# Rotating the height-free current on the full square: an obstruction

**Result.** The vertex-local current certificate, allowing arbitrary fixed
rotations, phase shifts, or even different current tables at every site,
does not by itself prove an upper bound below the residue-two target.
There is a rational feasible point of the vertex/edge local relaxation
with expected score `n²/3+n-2 = T+4/3` for every `n=3k+2>=11`.
This is *not* a grid tree or an improved construction.

## What the certificate tests

At each physical site keep a nonnegative normalized distribution on its
complete local star: its F/U label, the labels of its existing neighbors,
and the outgoing forced edge or no outgoing edge. Two perpendicular
neighbors cannot both be F; the four-cycle they force would be physical
even at a boundary vertex having these two neighbors. Exactly the edges
with at least one F endpoint are forced. Every forced edge points one
way, and a vertex sends at most one arrow. At the chosen root `(0,0)`
forbid any outgoing edge. These are necessary constraints: orient each
forced tree toward a sink, using the specified root in its component.

Impose exact equality of all **seven** shared edge-state probabilities
between its endpoints (both physical endpoint labels and the signed
direction, not only the probability the edge is present). No nonexistent
edge is included in the consistency constraints.

The file `analysis/research_program/square_current_obstruction.json`
stores a positive rational support of 257 local states over 81 vertex
types. To index each axis use four distinct near-boundary positions at
each end and one repeated interior position. A 10-square contains every
possible ordered pair of adjacent types, including repeated interior
types. The checker verifies all 162 directed-axis/type consistency tests,
atom legality, nonnegativity and normalization by exact rational arithmetic.
An LP on the 14-square produced the certificate; its numerical objective
is not needed for proof.

Summing the F marginal gives the exact score on each larger board:

    bulk:      (n-8)^2 / 3
    four side strips: (n-8) * 19/3
    corners:   82/3
    total:     n²/3 + n - 2.

Any proposed sum of linear inequalities valid on these local stars
also holds after averaging against this certificate. Arbitrary linear
edge charges cancel against a neighboring charge *only if their tables
agree in physical coordinates*. If different regions use different
tables, the certificate assigns their difference a definite expectation.
Thus no sum using only the stated local laws, additive boundary/cut
accounts and marginal agreement can have a universal right side
strictly below T. This quantifies the scope of the negative result:
it does not rule out a proof using a specially chosen global orientation,
conditioning on connectivity, integral case analysis, or stronger joint laws.

## Explicit four-sector rotated balance

Assign each site to its nearest side (tie order top, right, bottom, left).
Rotate the table from `HEIGHT_FREE_ROD_FLUX.md` clockwise with the side;
local column is respectively `c,r,n-1-c,n-1-r`. On a missing physical
edge evaluate the outward charge by appending a virtual U site: on a
boundary F it supplies an incoming arrow, and on a U the virtual edge
is unforced. This only evaluates the local inequality at a boundary
site; these virtual sites do not contribute to the score or consume
any physical outgoing slot. Sum the outward currents at each physical
vertex. Interior edges within a sector cancel exactly; keep both terms
on every cross-sector edge. Also keep the exact nonnegative vertex slack:

    5(3f-n²) = outer current + internal cut current - local slack.

At n=23 the root-consistent rational field gives `261 + 737/4 - 521/4
= 315`. The target corresponds to `5(3T-23²)=295`. In particular
neither simply treating the normals as rail backgrounds nor dropping
the internal sum is justified. All four physical corners are included.

## Checks beyond the primary obstruction

* Each unit square has a consistent distribution on its four labels;
  the 36 distinct *oriented* face cases also admit nonnegative joint
  distributions with the prescribed marginals on their two incident
  edges at each corner. These tiny LP witnesses are checked exactly.
  Testing one face at a time is not a global tiling.
* The marginal vector of undirected forced-edge probabilities passes all
  forest rank inequalities `x(E[S])<=|S|-1` at n=14,17,20,23,26,32.
  This finite-size extra check uses a single sink with capacity from u
  equal to its probability of no outgoing edge. Original directed arc
  capacities are their oriented edge marginals. For any nonempty S
  excluding the sink, outgoing cut capacity is precisely
  `|S|-x(E[S])`. For each possible source the checker finds a flow of at
  least one to the sink using integer-scaled capacities. Hence every
  nonempty S has cut capacity at least one. This is not asserted for all
  n by extrapolation. Even membership in the forest polytope of
  *marginal edges* does not couple the edges into the required vertex stars.

Replay without solving the large LP:

    python3 -B -m analysis.research_program.square_current --forest-cuts --faces

Omitting both switches gives the exact principal certificate, boundary
and cut calculation and the label-only face check, all solver-free.
`--generate` regenerates the small JSON certificate using `lp_solve`.
