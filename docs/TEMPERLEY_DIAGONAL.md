# Diagonal repetition and torus rigidity

Exploratory paper argument and deterministic finite checks; not a global square-grid upper bound.

## Bulk rigidity, without a period cutoff

Use an even doubled torus for a primal rectangular torus with both dimensions
at least 3. A midpoint paired with a primal vertex is an occupied primal edge.
Orient this edge out of its paired vertex. Each primal vertex sends one arrow.
Write F for vertices with all four incident edges occupied, U for the rest,
N for the number of primal vertices and f for |F|. Each F receives three
arrows, so N-3f is exactly the number of arrows into U.

No elementary face can have all four edges occupied: its dual face site
would have no partner. In particular an F cannot have perpendicular F
neighbors (the three F sites cover all four edges). Therefore the induced
F graph consists of straight wrapping rails and straight finite paths,
including singletons. Let p count the finite paths, not the wraps. There
are f-p edges internal to F. Each is oriented exactly once, so of the f
arrows out of F, exactly p land in U. Hence the exact periodic identity

    N - 3f = p + #arrows from U to U.

At equality there are no finite paths and all U send to F. Rails are
parallel, as perpendicular wraps intersect. Consecutive rails have spacing
at least three: spacing one makes a fully occupied face, and at spacing
two every intermediate vertex touches two F's; both incident edges would
have to be directed out of that U since all F send along the rails.
Spacing at most three follows since every U touches F. This includes the
single-rail case, measuring its gap to its periodic copy. Thus **all**
equality masks are period-three rails, for arbitrary rectangular periods.
A rail's longitudinal primal arrows run consistently in one direction.
The nonrail vertices point toward the rail; dually the forced pairs
leave a parallel cycle of face sites and midpoints per gap, with two
orientations. This gives the 96 doubled 12x12 tilings used by the census:
two axes, three phases and four independent binary orientations.

A finite-size consequence: on an m by m torus with no wrapping F rail,
each F path has at most m-1 vertices, so (m-1)(N-3f)>=f. In particular
N-3f>=ceil(N/(3m-2)). A sequence with bounded deficit on growing square
tori must eventually contain a wrap. This deduction does not transfer
directly to a punctured square with boundary.

## Frozen diagonal grammar

Take a 12-square central tile C from the side-17 witness on the doubled
board. Put C on the diagonal of a t by t tile array, a single saturated
periodic tile A above it, and B below it (also test the reflected diagonal).
If N,E,S,W are the outward port masks of C in increasing coordinate order,
then A must realize the vertical/horizontal pair (N,E) and B must realize
(S,W); the reverse diagonal exchanges E and W. Equal masks are necessary
and sufficient for joining two perfect-matching fragments along that side.
This only describes the interior, not the arms.

Of the 6,400 cut/root/completion tuples from the inverse-cross census, 968
admit exact interior joins. None of the 16 one-domino target cuts are among
them: at best they have four port-bit disagreements across the two filler
profiles. None of the 968 lets the four original arms repeat unchanged.
At each arm instead keep its original end piece and seek a repeatable
adapter with the same inner and outer profiles but using one chosen end
profile at both ends. Matching the remaining rectangle after reserving
the external domino endpoints is exact bipartite matching. For 800
tuples all four adapters exist; for 168 only two exist. End choice is
independent on each arm. No scoring optimality of the adapters is claimed.

## Explicit feasibility control

`python3 -B -m analysis.research_program.temperley_diagonal` reproduces the
census. `fixed_family(t)` uses bridge (3,4), root (0,0), cut (9,1), the
main diagonal and deterministic arm matchings initialized from surviving
old pairs. For t>=1 put one original corner in each corner, t pieces per
arm and the t by t interior above. Opposite port masks match by construction,
all interior sites have one partner, and the original corner root is the
only missing site. Thus the construction is renewable as a **tiling**.
Fixed-template replays for t=1..6 had preserved scores
110,174,264,378,516,678 (side 11+6t). Already t=2 misses 196 by 22.
These are direct evaluations of one prescribed family, not optimizations.
Port compatibility gets the area term but does not certify the linear
score; a useful successor must account for the loss along the interfaces.
