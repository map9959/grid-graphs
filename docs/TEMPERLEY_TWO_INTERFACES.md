# Two period-nine interfaces and one shared loss account

Scope: centered base-five arms; saturated rail layouts; parallel rising
diagonal interfaces with doubled tangential period 18. Each interface has
a fixed finite normal thickness with no prescribed bound. All end and
corner neighborhoods recur with bounded score variation. This is not a
bound on general grid trees.

## Fixed separation

Let A,B,C be the negative-normal, intermediate and positive-normal
backgrounds. The loss of the two joins is at least `d(A,B)+d(B,C)`,
where d is the minimum incoming-to-unpreserved cost of a periodic
interface between the specified layouts and phases. Conversely two finite
joins between matching layouts can be concatenated with a sufficiently
long homogeneous B region by translating the second join a whole period
in the normal coordinate. The two loss sums do not overlap. This is a
cylinder statement, not a guarantee about the finite square's caps.

The diagonal occupancy count is conserved every two doubled slices
(each step complements its count), so all middle layouts reachable from
the outer candidates must have nine incoming sites. This allows 120 of
384 layouts, including middle layouts without feasible physical arms.
Test **every ordered pair** of those 120 using the threshold-one
forward/reverse transfer, which searches arbitrary lengths. All 120
identities cost zero. None of the 14,280 nonidentical ordered pairs has
cost zero or one. A positive control is 14 -> 26 -> 50 with actual
distances two and two. Thus a *genuine* two-change path costs at least
four. Subtracting the independent arm minima from the target allowance
nine leaves at most three, on every `k mod 3`. Cases with an identity
leg are included: query both legs at thresholds obtained after subtracting
the other leg's known lower bound, then compare their sum against the
original allowance. No candidate is discarded by spending the same
allowance twice.

## Macroscopically separated parallel interfaces

Fixed separation is not the only geometry. Let the two lines have
normal offsets `s1*n+O(1), s2*n+O(1)` with -1 < s1 < s2 < 1, in primal
`r-c` coordinates. Suppose their matching rules repeat and the offsets
have fixed rates on the renewal subsequence (one may pass to a longer
subsequence for rational rates). End neighborhoods are bounded. Let
`B(x)` be the piecewise constant background at scaled offset x.
Write `TR(i)` and `BL(i)` for its top-plus-right and bottom-plus-left
period-nine arm minima. Over long growth, per nine added side units the
necessary lower bound on loss is

    integral_0^1 [ TR(B(-z)) + BL(B(z))
                  + sum_{j: |s_j| <= z} d_j ] dz .

Indeed, normalized offset runs from -1 to 0 on each of the top and right
sides and from 0 to 1 on the other two. Interface j has longitudinal
length `(1-|s_j|)*n+O(1)`, giving coefficient `1-|s_j|` to its per-period
loss. Integrating the indicator of `|s_j|<=z` gives exactly that
coefficient. The formula is an asymptotic slope statement, insensitive to
bounded end corrections, not a claim about a single small square.

For almost every z the integrand is a shared account for the background
path from `B(-z)` to `B(z)`. If there are no changes, `TR+BL>=18`; if
there is one, the period-nine transfer excludes total <=9. If there are
two genuine changes, each costs >=2 and the outer arms alone cost >=6.
Thus the integrand is >=10 and the target permits only 9. The same
argument applies to any fixed finite number of parallel interfaces under
the same repeating-background/arm hypotheses: either zero or one genuine
change, or at least two. The arm-contacting layouts are in the balanced
sector for all three residues (also directly checked).

As a separate finite check at `s1=-1/2,s2=+1/2`, a side increase of 18
adds one period per interface, one outer period per side and four middle
side periods in total. The relaxed integer cost for the two steps is

    TR(A)+BL(B)+d(A,B) + TR(B)+BL(C)+d(B,C).

The program minimizes its lower bound over the 120³ triples, allowing
the two arms at a corner to optimize independently. It is >=26 versus
the allowed 18, before demanding any matching cap. This calculation uses
only the threshold-one distances; 26 is not asserted attainable.

## Replay

    cargo build --release --offline --bin diagonal_nine
    python3 -B -m analysis.research_program.two_interfaces

There are 708 eligible ordered outer pairs per residue, 84,960 triples
per residue before pruning, and no target survivors. The code reuses
the period-nine transition engine and queries new middle-background
pairs. No square optimized above the project's search limits is needed.
