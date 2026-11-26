# Oblique two-background interface, primal period (3,6)

**Result:** no target-rate join on either parity of k. This is a single
straight interface with a periodic matching of arbitrary fixed normal
width and saturated exterior backgrounds. Physical arms can have independent
arbitrary fixed depth and six-primal-site tangential period. Corners/end
neighborhoods are bounded on the renewal subsequence. No unrestricted
tree bound is claimed.

## Backgrounds and growth budget

Use legacy IDs from the 96 period-six torus layouts. Sixty are invariant
under doubled translation (6,12). This enumerates the saturated choices:
straight parallel rails at spacing three; the primal/dual longitudinal
direction bits are constant along each rail. Horizontal rails each repeat
after one rail gap under this translation (12 layouts), vertical ones
after two gaps (48 layouts).

For normalized seam `row = column/2 + s`, measure coordinates in side
units. First take `0<=s<=1/2` so it traverses the full width. A side
increase of 24 gives four interface periods, complete six-site periods
on both physical horizontal sides, and fixed residue phases on the
vertical sides for s=0,1/4,1/2 (asymptotic rates suffice otherwise).
Use A above, B below, with per-period arm minima T,R,Bot,L. The remaining
shared allowance for the **four copies** of the interface is

    24 - 4*T(A) - 4*Bot(B)
       - 4*s*L(A) - (4-4*s)*L(B)
       - (4*s+2)*R(A) - (2-4*s)*R(B).

The total allowance 24 comes from the exact preserved-vertex ledger, or
from subtracting `3*T(k)` from `n^2+4n` at the old and new sides.
Equivalently the desired score increment over this comparison is
`T(k+8)-T(k)=48k+248`. A favorable starting constant cannot compensate
for a recurring shortfall.

The minima of the four arms were computed by the tangential column
matching DP. For each parity, an independent normal-direction transfer
(`arm_depth --six`) tested whether *any* finite depth improves the result.
The loss residue is fixed modulo three by the background cut flux, so a
strict improvement must save at least three. No improvement was found.
Costs across the 60 layouts times four sides: 40 zero, 12 two, 24 three,
12 four, 80 six and 72 unbalanced/impossible. The least homogeneous
four-arm sum is 12 against an allowance of 6.

## Oblique transfer

Slice the doubled cylinder by `z=2*r-c` and index sites by `r mod 6`.
A forward horizontal domino ends at the same index on z+1; a forward
vertical domino ends one index higher on z+2. The frontier therefore
also retains pending vertical arrivals one slice ahead. Enumerate all
partitions of the free sites between the two forward directions, rejecting
collisions. Keep the vertical-match bits on midpoint sites of the last
four slices. At an even z, a primal vertex on slice z-2 has its vertical
midpoints on z-4,z and its horizontal midpoints on z-3,z-1. All are
now known. Charge 1,2 on degrees 2,3; otherwise charge 0.

The state includes z mod 12. Cuts can be padded into the half-plane
backgrounds to that phase at zero loss. Nonnegative costs justify
retaining the cheapest visit per state, not imposing any width cutoff.
The Python and packed Rust traversals agree on all distance queries
and reached-state counts at threshold one. The Rust run additionally
tested threshold three. Forbidden by a threshold is not an exact distance.

At centered `s=1/4`, on both parities only five ordered pairs survive
the arm test, out of 3,600. The same five and budgets occur at s=0,1/2:

| A -> B | allowed loss per seam period | measured minimum |
|---|---:|---:|
| 6 -> 38 | 0 | >=4 |
| 24 -> 25 | 0 | 3 |
| 24 -> 38 | 1 | >=4 |
| 24 -> 56 | 0 | >=4 |
| 39 -> 38 | 0 | 3 |

For every fixed ordered pair, total loss is affine in s on [0,1/2].
Since the target fails at both ends for every pair, it fails throughout
that interval. For an interface clipped by an adjacent pair of sides,
the cost is likewise affine in the intercept between successive
corner crossings: arm-segment lengths and interface length are affine.
The remaining limiting endpoints are homogeneous squares (the line
just touches one corner); their arm cost also exceeds target. This
extends the negative slope test to fixed scaled intercepts, under the
same periodicity and bounded-end assumptions. This argument does not
cover a bent interface or a growing transition region.

## Replay

    cargo build --release --offline --bin arm_depth --bin oblique_cost
    python3 -B -m analysis.research_program.oblique_rails

Nonidentical controls include 39 -> 75 at cost one, 6 -> 24 at cost
two and 24 -> 25 at cost three; all 720 homogeneous phase steps were
also verified. There is no affordable transition for which to test
end caps, a recurrence, or parity seeds.
