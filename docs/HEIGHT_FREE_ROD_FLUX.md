# A height-independent flux certificate for the sheared rod core

**Theorem (tested rod-and-frame geometry).** Let p be the number of
three-column triples in a repeat. Allow all labels in all three columns
to vary in any finite-height diagonal pocket. Above it the immutable
vertical rods have column phase 1 mod 3; below it they have phase 0.
Let delta be the change in the number of core centers relative to Q,
and M the number of rod vertices spending an outgoing edge in the core
under the orientation of the nine-row rod account. Then

    5(delta-M) <= -p.

Consequently the paired frame and core net G is at most
`8p-ceil(p/5)`. This holds simultaneously for all heights and periods.
It does not prove the unrestricted square-grid conjecture. In particular
it uses both specified far phases, the shearing translation `(3p,3p)`,
the core debit relative to Q, and the frame inequality `N+M<=8p`.

## 1. Orienting the stars before taking the cut

Every edge incident to a chosen center F is forced. A feasible periodic
quotient component is a tree or has one winding cycle. Orient toward a
root or toward and around that cycle; hence every vertex has at most one
outgoing edge. In the core restriction mark as paid exactly the rod
vertices whose outgoing edge is in that restriction. This is the same M
charged to the frame, not a separately chosen count.

For the core calculation alone expand each contracted rod star into its
semi-infinite rod with pendant unselected neighbors, using homogeneous
padding as necessary. If its contracted vertex has an outgoing core edge,
orient its internal tree edges toward the actual attachment vertex
supplying that edge. Otherwise orient the internal tree toward the
homogeneous end at infinity. Other core edges retain their orientations.
This is periodic in the shearing translation, and spends at most one
outgoing edge per physical vertex. This extension need not orient the
frame itself a second time. Far up the upper rods the axial arrows are
south for paid rods and north otherwise; far down the lower rods they
are north for paid rods and south otherwise. There all U leaves point
into their neighboring rail. Different rods may have different choices.

## 2. The local inequality

Assign an integer current to each east or south unit edge, **including
unforced edges**. The latter current is bookkeeping, not a forced arrow.
Look up the column of the west/north endpoint modulo 3 and the two
endpoint labels in that order. `+` means the forced arrow points east or
south; `-` means it points in the reverse direction.

| edge | UU | UF- | UF+ | FU- | FU+ | FF- | FF+ |
|---|---:|---:|---:|---:|---:|---:|---:|
| E, col 0 | 1 | 1 | -5 | 7 | -2 | 4 | -2 |
| S, col 0 | 6 | 6 | 0 | 12 | 6 | 12 | 0 |
| E, col 1 | 2 | 2 | -4 | 5 | -1 | 2 | -4 |
| S, col 1 | 0 | 0 | -6 | 6 | 0 | 6 | 0 |
| E, col 2 | 0 | 0 | -3 | 6 | 0 | 6 | 0 |
| S, col 2 | 0 | 0 | -3 | 3 | 0 | 3 | -3 |

At every interior vertex,

    J_east + J_south - J_west - J_north >= 5*(3*1_F - 1).       (1)

This is a finite integer inequality. The four neighbors cannot include
two F sites in perpendicular directions: those two sites force a unit
face cycle, regardless of the central label. Enumerate all remaining
neighbor masks, either central label, and either no outgoing arrow or
one along any forced incident edge. Every other forced edge points in.
For the three residues this gives 150 checks, all with nonnegative
slack. Both endpoints consult the same table for their shared edge.
The optional LP search *found* the table; the proof only needs these
integer checks.

## 3. Sheared cut sum and normalization

Let `d=row-column`, take a full longitudinal period of the strip
`L<=d<=R`, and put `s=R-L+1`. Choose the cuts far enough out that the
exterior arrows above are homogeneous there. Each slice has 3p sites.
On a cut toward increasing d the signed current is south minus east
(the east edge enters the lower-d side). Equivalently the cut has one
outgoing south and one outgoing west edge per column, the latter with
minus its east current. Indices of the west edges are shifted by one
column, immaterial when summing the full period. Thus the sum of the
left side of (1) is `Phi_lower-Phi_upper`. Internal and longitudinal
edges cancel exactly.

For each triple the sum of the horizontal currents depends only on
the phase: every horizontal F-U edge has its arrow from the U leaf.
Only the single vertical FF edge's current depends on that triple's
rod direction. The exact currents and price are:

| upper, lower direction | Phi_upper | Phi_lower | paid | Phi_upper-Phi_lower+15*paid |
|---|---:|---:|---:|---:|
| S, S | 6 | -6 | 1 | 27 |
| S, N | 6 | 6 | 2 | 30 |
| N, S | 12 | -6 | 0 | 18 |
| N, N | 12 | 6 | 1 | 21 |

In particular `Phi_upper-Phi_lower+15M>=18p`. This is where the
direction of the phase change matters.

In reference Q a normal slice has p centers except at d=1, where it
has none. In fact the three column residues contribute respectively
bottom-rod centers for `d>=2`, top-rod centers for `d<=-1`, and the
singleton for `d=0`. Hence the strip has `(s-1)p+delta` selected sites.
Summing (1) now gives

    15(delta-p) <= Phi_lower-Phi_upper <= 15M-18p.

Rearranging gives the theorem. Another full free slice changes the
reference count by p; it does not change either cut current. No
assumption that a fixed-height state vector will eventually stabilize
is involved. The ordinary tangential three-lane frame potential gives
`N+M<=8p` (`NINE_ROW_ROD_ACCOUNT.md`), completing the net bound.

## Checks

    python3 -B -m analysis.research_program.height_free_flux --witnesses
    python3 -B -m analysis.research_program.frame_root_price --witnesses

The first command verifies the integer table, the four cut-current
cases, and actual local and summed inequalities on the uncontracted
period-two and period-three witnesses. Their M=0 orientations have
delta=-1, divergences -36 and -54, and total nonnegative slacks 9
and 6. The resulting upper bounds 15 and 23 are attained. Neither
witness supplies the required target growth.
