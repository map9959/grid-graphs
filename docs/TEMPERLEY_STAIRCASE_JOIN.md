# Alternating slopes in one repeat

Tested a sawtooth whose primal tangents in each repeat are `(3,3)` and
`(-3,3)`. This is **not** a sum of two separate asymptotic seam costs:
one tip and one trough occur every six columns, and their matching and
primal component data are part of the repeating state. There are two
saturated backgrounds (above/below); the physical arms have period six
and arbitrary fixed depth. End caps have bounded score variation on each
renewal subsequence. The global target is still open.

## Shared account

For side increase 12 the target permits 12 additional units of
boundary deficiency plus incoming arrows into unpreserved sites. Write
`s` for the mean interface height as a fraction of the side, A for the
upper background, B for the lower one. In terms of six-site arm minima,
the necessary inequality is

    2*T(A) + 2*Bottom(B)
      + 2*s*(L(A)+R(A)) + 2*(1-s)*(L(B)+R(B))
      + 2*D_wave <= 12.

The period is measured by *horizontal translation*, not the sum of the
lengths of the two sloping legs. D_wave counts the loss of the entire
interface per translation. All 96 saturated period-six layouts are
eligible as inputs; the normal arm transfer independently checks that
no finite depth improves their arm costs.

For each k parity the centered test leaves only 36 of 96² ordered pairs,
each with D_wave allowance zero. They all require a change between two
different phases of horizontal rails. At s=0 and 1 the limiting arm
accounts each leave 96 ordered pairs, again requiring that phase change
at zero loss. These limiting calculations keep the arm costs as approached
from inside the square; they do not delete a thin component and reoptimize
a different geometry.

## Single connected transfer

On the doubled board use `z = row - g(column)`, where
`g(c)=min(c mod 12,12-(c mod 12))`. A physical neighbor changes z by
exactly one, even at the two bends. A site arriving at the frontier is
already matched; at every other site choose a forward partner. Enumerate
the choices jointly, including the column 11/0 join, rejecting all
destination collisions. At the two turns the number of forward neighbors
differs; they are not spliced from independent straight-seam matchings.

The state carries the matching ports, the preceding midpoint labels,
the normal phase and the partition of the six primal frontier sites.
Horizontal primal edges on a descending piece arrive at the next
frontier; edges at the peaks go to **both** sides. Each occupied edge is
joined once. Component identifications include a signed period shift:
sites connected to different translates of the same site are not
silently identified. A component with one cycle of nonzero winding is
allowed (it lifts to an acyclic graph); a contractible cycle or two
independent cycles in one component are not. The latter have a finite
cycle in the lift since the winding group is cyclic. This is necessary
connectivity data, not a declaration that any accepted partial state
extends through square corners.

At each primal vertex all four incident edges are now known. Charge
`0,1,2,0` at degrees `1,2,3,4`. Exhaust each zero-loss source closure
without limiting normal width. Accepting a destination even without
requiring a particular final partition favors the proposed family.
No eligible background pair connects. The 96 homogeneous controls
reproduce the identical matching phase and component partition after
a full normal repeat; all 576 two-slice control updates were verified.

## Why moving the bend cannot fix the zero-loss phase change

There is also a geometric explanation. Pad a hypothetical zero-loss
interface into the two homogeneous backgrounds to obtain a complete
infinite tiling periodic along the horizontal axis. Every unpreserved
vertex receives no arrows, so its single outgoing edge ends at a preserved
vertex. Every preserved vertex sends to another preserved vertex.
Preserved paths cannot bend because three preserved sites around a
square leave its face without a domino partner. A finite preserved path
is impossible: its vertices would send more internal arrows than the
path has edges. There can be no infinite vertical preserved path or ray
either: sufficiently far above and below the strip the backgrounds
consist of horizontal rails. Every preserved path is thus a complete
horizontal rail. Every intervening unpreserved site must touch exactly
one rail (each incident rail edge is occupied and cannot point into
the unpreserved site). Consecutive rails therefore have spacing three:
adjacent rows would fill a whole face, spacing two gives two neighbors,
and larger spacing leaves a site with none. The phase at the two ends
must agree, contrary to every arm-eligible pair. This argument does not
presume that each short sloping piece looks like an isolated straight
interface.

The fixed-pair loss rate is affine in s. Failure at both limiting heights
also excludes intermediate scaled heights, with bounded end corrections.
The result does not exclude nonhorizontal net translation or an interface
network with different boundary payments.

    cargo build --release --offline --bin arm_depth
    python3 -B -m analysis.research_program.staircase_join
