# Paper Zero-Loss Upper Bound

Date: 2026-09-07. **Independently reviewed paper proof, not a Lean theorem.**
One read-only review checked the phase, bad-edge, and singleton classification;
a second checked the full physical-contact argument and both numerical bounds.
Neither found a fatal gap. No kernel verification is claimed.

## Scope

Use the notation and fixed orientation of the
[half-coefficient paper](PAPER_HALF_COEFFICIENT_UPPER.md) and
[packing-stability note](PAPER_PACKING_STABILITY.md). The paper conclusion
is restricted to the exactly saturated case:

```text
n=3k+2, k>=3, Q=k-1, N=n-4=3Q+1, T=3k^2+7k,
Lambda=Q(N-1)-GOOD=0  ==>  f<=T+3.
```

With the previously formalized missing-side/coverage input, the stronger
paper consequence for `k>=5` is `f<=T+1` in this same zero-loss case.
The contact, singleton, and active-phase arguments are reviewed paper proofs,
not imported Lean lemmas. The reviewed obligations are retained at the end
as safeguards for any later formalization.

There is no assertion of a global constant upper excess for arbitrary
`Lambda`, no positive-loss extension, and no constant-gap lower claim.
The separately proved endpoint-strip result concerns the reduction described
in [Endpoint Free Column](PAPER_PACKING_STABILITY.md#endpoint-free-column).
It is a separate input/result, not a proof of the mixed active phases,
singleton localization, or physical contacts needed here. This draft does
not use that strip result as a black box to discharge those obligations.

## Notation

Physical coordinates are `(x,Y)` in `{0,...,n-1}^2`. Deep rows have indices
`y=1,...,N`, meaning physical row `Y=y+1`; column coordinates remain
physical throughout. The deep column interval is `I=[2,3Q+2]`. A vertical
step `t` joins deep rows `t,t+1`, for `1<=t<=N-1=3Q`.

The preserved set is `F`, its complement is `U`, and the forced graph has
every grid edge with at least one preserved endpoint. It is a forest.
Every actual induced `F` component is a straight filled interval, possibly
a singleton. Write `r=p+h+d` for pure, shallow, and deep carriers as in the
companion papers; convex trimming identifies `d` with the number of actual
induced deep components. Write `c` for the ambient forced component count,
including isolates, and `b` for the weighted boundary-hole deficiency.

Let `A` denote the two-layer annulus as a vertex region, not an auxiliary
mirror graph. Put `F_A=B+E=4n-4-K`, where the scalar `E` counts preserved
next-ring vertices. Subscripts distinguish the edge sets `E_y` below from
that scalar. The excess `e=f-T` is a signed integer. We use

```text
3f+r+c+b=n^2+4n,
3e+r+c+b=3Q+15,
Z=d+BAD+GOOD.
```

Good horizontal deep edges exclude deep rows `1,N`; good vertical deep
edges exclude physical columns `2,3Q+2`. Define `E_y` to be the physical
left-column set of good horizontal edges in deep row `y`, with `E_y=empty`
outside `2<=y<=N-1`. Define `V_t` to be the physical column set of good
vertical edges at step `t`, and `v_t=|V_t|`.

All intervals of indices below are integer intervals. A range with no
indices is empty. A horizontal or vertical *core* means a nontrivial actual
deep component with an edge in the indicated orientation, not a virtual
rod obtained by filling a gap.

## Fourth-Step Propagation

Fix the residue schedule on every good horizontal row, including empty rows:

```text
T_y=[y-1,y+1] if y=2 mod 3,
T_y=[y-2,y]   otherwise,
A_t=union_{y: t in T_y} E_y,
delta_t=3(Q-v_t)-|A_t|.
```

The local cycle exclusions in the half-coefficient proof say that distinct
vertical axes at a step are at least three apart; `E_y,E_z` are disjoint
when `0<|y-z|<=2`; and `E_y` is compatible with `V_t` throughout the valid
portion of `[y-2,y+1]`. Compatibility means that all horizontal endpoint
columns avoid the blocks `[x-1,x+1]`, `x in V_t`.

Here is a useful insertion version of the joint step bound. If `B` is any
additional compatible set of edge-left columns, the same path count applied
to `A_t union B` gives

```text
|A_t union B|<=3(Q-v_t),
|B minus A_t|<=delta_t.                              (1)
```

Indeed a nonempty edge set on a path uses at least one more endpoint than
edges, disjoint from the `3v_t` vertical-block columns. For an empty union
the inequality follows from integral vertical packing. No disjointness
between `B` and `A_t` is assumed.

The scheduled row sets are pairwise disjoint at each step, and each edge
is counted three times. Consequently

```text
delta_t>=0,
sum_t delta_t=3Lambda.                              (2)
```

For a row `y`, the fourth, omitted step is

```text
o(y)=y-2 if y=2 mod 3,
o(y)=y+1 otherwise,
```

whenever this lies in `[1,N-1]`. At that step take `B=E_y` in (1). Of the
rows scheduled there, every row within distance two of `y` has an edge set
disjoint from `E_y`. The only remaining possible contributor is

```text
sigma(y)=y-3 if y=2 mod 3,
sigma(y)=y+3 otherwise.
```

For either a residue-zero or residue-one row `y`, the assigned rows at
its omitted step are `y+1,y+2,y+3`, restricted to valid good rows. For a
residue-two row they are `y-3,y-2,y-1`, again restricted to valid rows.
Thus the nearby sets drop out and

```text
|E_y minus E_sigma(y)|<=delta_o(y).                  (3)
```

The omitted map is injective: rows of residues `2,0,1` map respectively
to steps of residues `0,1,2`, and each formula is a translation within its
residue class. In particular these propagation errors cannot repeatedly
charge the same step. Only the zero-error consequence is used below.

Assume henceforth `Lambda=0`. Then all `delta_t=0`, and (3) yields

```text
E_3 subset E_6 subset ... subset E_(N-1),
E_2 superset E_5 superset ... superset E_(N-2).
```

Every good residue-one row is empty. Its forward inclusion chain ends at
`y=N-3`, whose omitted step `N-2` is valid and whose successor row is the
invalid good row `N`, with `E_N=empty`. Backward propagation empties the
entire chain. Row `2` has no valid backward omitted step and row `N-1`
has no valid forward omitted step; neither endpoint is used illegally.

## Bands And Phases

For `a=0,...,Q-1` call steps `3a+1,3a+2,3a+3` band `a`, and write

```text
U_a=E_(3a+2), D_a=E_(3a+3).
```

Here `U_a` is a row-edge set, not the hole set `U`. Empty residue-one
rows imply `A_t=U_a union D_a` on all three steps of the band.
The `U_a` shrink with `a`, and the `D_a` grow.

At an active zero-loss step the exact stability partition gives
`rho_t=1,w_t=0`. Moreover `U_a` and `D_a` cannot both be nonempty.
They are disjoint, and for their union to be consecutive there would be
consecutive left columns belonging to different adjacent rows. The two
corresponding edges have endpoints diagonally opposite in a cell, forcing
a four-cycle. Shared left columns already force the parallel-edge cell
cycle. Thus the sole nonempty set is itself one consecutive edge interval,
and it is one actual horizontal carrier interval in its own row.

The active bands therefore consist of a prefix of `p_U` upper-row bands,
then `L` empty bands, then a suffix of `q_D` lower-row bands:

```text
p_U+L+q_D=Q,
number of horizontal cores=Q-L.                     (4)
```

We use `p_U`, rather than `p`, for the prefix length to avoid collision
with the existing pure-carrier count. These are the prefix `p` and suffix
`q` in the informal band description. Each rod lies on a different row
and different rods are separated by at least three rows.

An active endpoint interval and its exact vertical-axis set have the form

```text
J=[2+3i,2+3j], 0<=i<j<=Q,
P(i,j)={3r:1<=r<=i} union {3r+1:j<r<=Q}.             (5)
```

To see this, tile from each endpoint of `I` with the consecutive disjoint
three-column vertical blocks until reaching the one horizontal endpoint
interval. There are no vacancies, so both interval endpoints are `2`
modulo three. The interval has `3(j-i)+1` vertices, and its complement
has exactly the axes in (5). The three steps have the same interval and
hence exactly the same axes.

An inactive step has `Q` axes. Ordering them gives `x_r=3r+epsilon_r`,
where the spacing and endpoints force a nondecreasing sequence
`epsilon_r in {0,1}`. Thus for a unique `s in [0,Q]` its axes are

```text
P_s=P(s,s), with sole free column 2+3s.              (6)
```

Two consecutive inactive steps have the same `s`. A phase change would
place axes `3r` and `3r+1` on the two steps at their shared preserved row;
the adjacent preserved vertices together with a vertical edge force a cell
cycle. The same shared-row obstruction applies to adjacent active steps.
In particular their intervals must intersect:

```text
max(i,i')<=min(j,j').                               (7)
```

If, for example, `j<i'`, the old right axis `3j+4` and new left axis
`3j+3` are adjacent at the shared row, giving that cycle. The reverse order
is symmetric. An active interval adjacent to an inactive phase `s` must
contain `2+3s`: otherwise the same adjacent-axis obstruction occurs.
These arguments include adjacency across band boundaries.

Within the upper prefix, shrinking endpoint intervals can only add axes.
Within the lower suffix, growing endpoint intervals can only remove axes.
At the middle interface, (7) prevents an axis from changing between its
left and right residue classes. Each occurring axis consequently supports
one uninterrupted interval of vertical edges: it is born only as an upper
interval shrinks and dies only as a lower interval grows. It has at most
one actual vertical core.

If `L>0`, the middle has one phase `P_s`, and nesting plus the interface
condition makes all other axis sets subsets of `P_s`. Every axis of `P_s`
occurs, so there are exactly `Q` vertical cores.

If `L=0`, let `J_0` be the intersection of the last upper interval and the
first lower interval. When one prefix/suffix is absent, use just the last
upper interval or first lower interval, respectively. The intervals
intersect by (7), and

```text
J_0=[2+3i_0,2+3j_0], m=j_0-i_0>=0, |J_0|=3m+1.
```

The union of all occurring axes is `P(i_0,j_0)`: nesting reduces the union
to the two central sets, and their union leaves precisely their common
endpoint interval. There are therefore exactly `Q-m` vertical cores.
In the one-orientation case the central interval is active, so `m>=1`.

## No Bad Edges

We next exclude actual bad deep edges; they cannot be silently deleted
when counting components.

A bad vertical edge at extreme column `2` or `3Q+2` is incompatible with
an active horizontal interval touching that extreme, by the four-step
horizontal shadow. If the interval does not touch that extreme, the
nearest vertical axis is at distance one or two (`3` or `4` at the left,
and the reflected choices at the right). Parallel vertical edges at those
distances force a four- or six-cycle. In an inactive phase the same two
possibilities for the nearest axis apply, including an endpoint free
column. Hence no bad vertical edge exists.

For a bad horizontal edge on deep row `1`, use step `1`; for one on row
`N`, use step `N-1`. Its endpoints must avoid every vertical block by the
same diagonal/cell exclusion. An inactive step leaves only one column,
which cannot contain an edge. An active step leaves just `J`, so the bad
edge lies in `J`. The actual horizontal rod in that boundary band fills
every edge of `J` and lies one or two deep rows from the bad edge. The
matching left column gives a four- or six-cycle. Therefore

```text
BAD=0.                                             (8)
```

Every nontrivial deep component is now one of the good horizontal or
vertical cores counted above. All remaining deep components are singleton
deep intersections, whether or not the full carrier extends into `A`.

## Singleton Localization

Consider the four deep rows `3a+1,...,3a+4` of an active upper band.
Inside its `J`, the filled horizontal bar occupies row `3a+2`. Rows
`3a+1,3a+3` contain no additional preserved vertices in `J`: a vertex
there is adjacent to the bar and forms a preserved bend or is diagonally
opposite one of its endpoints. Thus only outer row `3a+4` can hold a
singleton in `J`. Outside `J` the exact vertical blocks leave only the
actual vertical axes available for preserved vertices. The lower-band
argument is reflected: its bar is on `3a+3`, and its only potential
singleton row inside `J` is outer row `3a+1`.

Compare consecutive upper bands. The candidate outer row of the earlier
band is the first row of the later band; the later bar excludes it inside
the later interval, while outside that interval a preserved vertex must
lie on a later vertical core. The shrinking inclusion ensures this covers
every candidate. Consecutive lower bands work in reverse. At an inactive
band only its free column can contain a singleton, because the other
columns are vertical axes or their forbidden immediate neighbors.

These comparisons leave just the central corridor or transition:

```text
L>0: column 2+3s, rows [3p_U+1,3(p_U+L)+1];
L=0: row 3p_U+1, columns in J_0.
```

At an active/inactive interface the free column belongs to the active
interval, so the descriptions agree at their shared row. At a direct
upper/lower interface both outer-row conditions hold, giving the
intersection `J_0`, not the union. If a prefix or suffix is absent, the
first or last deep row is exactly the indicated transition row.

Singletons in either of these one-dimensional intervals are at least three
positions apart. In the corridor, a nearest vertical rail is two columns
away, including when the free column is extreme. Two preserved vertices
at row distance one or two, together with the rail segment and their
two-edge transverse contacts, force respectively a six- or eight-cycle.
All perimeter edges are forced: the rail is preserved, the transverse
paths have preserved endpoints, and a length-two free-side segment has
preserved endpoints. If two vertices were consecutive, they would also
contradict (8) or the absence of a vertical core in the free column.

At the transition, a horizontal bar is two rows away and spans `J_0`.
Use the same six-/eight-cycle argument with the axes interchanged. There
is at least one such bar even in the prefix-only or suffix-only case.
Thus, writing `s_D` for the number of singleton deep components,

```text
L>0: s_D<=L+1, since the corridor has 3L+1 positions;
L=0: s_D<=m+1, since J_0 has 3m+1 positions.
```

Together with (4) and the vertical-core counts, this proves the proposed
component estimate

```text
L>0: d=(Q-L)+Q+s_D<=2Q+1,
L=0: d=Q+(Q-m)+s_D<=2Q+1.                           (9)
```

## Physical Contacts

Select two literal contacts for each actual deep component. A contact is
either an edge from that component to `A`, or a two-edge path through one
deep hole to a different deep component. Both edges of the latter path
are forced. The following selection specifies endpoints, rather than
postulating two abstract attachments per carrier.

For a horizontal core with interval `[2+3i,2+3j]`, its internal left end
contacts the axis `3i` through column `3i+1`; its internal right end
contacts axis `3j+4` through column `3j+3`. Use the row of its bar. The
target lies strictly inside the vertical core, since that axis occurs on
all three steps of the band and the bar is on an interior band row. An
end at a deep side boundary instead uses its outward edge to `A`.

For a vertical core, an internal birth at a shrinking upper interface
occurs on shared row `3a+1`; the preceding upper bar is on row `3a-1`.
The same column gives a two-edge contact through row `3a`. An internal
death at a growing lower interface is reflected, using the next lower
bar two rows later. A disappearing/appearing axis lies strictly inside
the relevant bar: axis columns are `0` or `1` modulo three, while bar
endpoints are `2` modulo three. If the core reaches the first or last
deep row, use its outward edge to the annulus instead. This also covers
birth/death at the direct central interface; an axis cannot switch its
residue class there by (7).

For a singleton in an `L>0` corridor, use its two transverse contacts to
the flanking rails, each at distance two. For an extreme free column,
replace the missing rail contact by the outward edge to the side annulus.
For a singleton in an `L=0` transition, use the bars two rows above and
below. If `p_U=0` or `p_U=Q`, replace the missing bar by the outward edge
to the top or bottom annulus. For the all-inactive case `L=Q`, the corridor
rule still applies.

Here are the disjointness checks required to use these selections in a
forest rank count. They refer to the entire phase sequence, not just the
band in which a contact was selected.

- Horizontal-end connectors have gap columns `3i+1` on the left or
  `3j+3` on the right. No such column is an occurring vertical axis.
  Within each nested family this follows from the side's fixed residue;
  across the transition the common interval condition prevents a gap
  from becoming an opposite-side axis.
- Vertical-end connectors have occurring vertical-axis columns. They are
  therefore disjoint from horizontal-end connector interiors. A single
  core has distinct birth and death connectors, and different cores on
  different axes cannot share one.
- Corridor-singleton contacts have rows in the central corridor, where
  there are no horizontal bars, and their interior columns are gaps, not
  occurring axes. Distinct singleton rows make their interiors distinct.
- Transition-singleton contacts have columns inside `J_0`, where no
  vertical axis ever occurs. Their connector rows are the transition row
  plus or minus one, neither of which contains a horizontal bar. Distinct
  singleton columns make their interiors distinct.
- Outward annulus contacts have no interior vertex. Each annulus vertex
  has at most one neighbor in the deep square, so distinct deep boundary
  vertices cannot select the same boundary edge or endpoint there.

Every length-two connector interior is a hole, since a preserved interior
would extend an actual carrier or create a preserved turn, contradicting
the component description. The preceding separation also prevents reuse
of any physical edge. A singleton contact can target the endpoint of a
core, but it arrives perpendicularly to that core's own outgoing endpoint
contact; it does not duplicate that contact. Contacts that target strict
interiors of cores likewise cannot be their outgoing endpoint contacts.
Thus the selection contains exactly `2d` distinct contacts with pairwise
disjoint interiors, avoiding the retained component vertex sets.

Let `H_A` be the actual forced subgraph induced on all annulus vertices,
including its isolates, and let `c_A` be its component count. Retain
`H_A`, the actual induced trees of the `d` deep components, and the selected
contacts. This is a literal subgraph of the forced forest; no `UU` mirror
edge or virtual boundary-path edge is added. Contract each retained
component tree and suppress the disjoint hole interiors of contacts.
The resulting graph is a forest with

```text
vertices=c_A+d, edges=2d.
```

A loop or parallel pair would lift to a forced cycle and is impossible.
The forest bound therefore gives

```text
c_A>=d+1.                                          (10)
```

This is the physical-rank step. Counting two nominal contacts without
the distinctness and interior checks above would not establish (10).

Equivalently, avoid contraction entirely. If Z counts deep F vertices and j
counts the selected contacts' interior U vertices, the retained graph has
`|A|+Z+j` vertices and
`(|A|-c_A)+(Z-d)+(2d+j)` edges. The three edge families are disjoint.
The nonempty forest edge bound again gives `c_A>=d+1`. This count retains
annulus isolates and does not identify full global carriers across the cut.

## Annulus Ledger

Let `r_A` count components of the actual induced preserved graph in `A`.
Let `C_o` count preserved outer corners and `C_i` preserved corners of
the inner perimeter of the annulus, namely `(1,1),(1,n-2),(n-2,1),(n-2,n-2)`.
The annulus has `8n-16` vertices. Its degree sum over preserved vertices is

```text
4F_A-(B+C_o)-(E-C_i)=3F_A-C_o+C_i.
```

The induced preserved annulus forest has `F_A-r_A` edges. Subtracting
these once from the degree sum gives `2F_A+r_A-C_o+C_i` forced annulus
edges. Its exact forest ledger is consequently

```text
c_A=2K-8-r_A+C_o-C_i<=2K-4-r_A.                    (11)
```

The isolates in `H_A` are essential to this identity. This `c_A` is not
the component count of the virtual mirror paths in the stability note.
If `F_A` is nonempty, `r_A>=1`, so (10)--(11) imply

```text
2K>=d+6.                                           (12)
```

## Zero-Loss Bound

By (8), zero loss, and the original deep identity,

```text
f=F_A+GOOD+d
 =4n-4-K+3Q^2+d
 =T+6+d-Q-K,
e=6+d-Q-K.                                         (13)
```

If the annulus contains a preserved vertex, (12), then (9), give

```text
2e=12+2d-2Q-2K<=6+d-2Q<=7.
```

Integrality yields `e<=3`. If `F_A=0`, use (9) directly instead:

```text
f=3Q^2+d<=3Q^2+2Q+1<T=3Q^2+13Q+10.
```

Thus both annulus cases give the stated `Lambda=0` paper bound `f<=T+3`.
No estimate in this section substitutes good-graph component
counts for actual deep components before establishing `BAD=0`.

## Stronger Covered Consequence

**Reviewed paper consequence; includes the checked coverage dependency.**
Assume `k>=5` and `e>0`. The previously formalized missing-side closure,
as recorded in the [half-coefficient source anchors](PAPER_HALF_COEFFICIENT_UPPER.md#source-anchors),
is used here to conclude that every open side is covered by a pure carrier.
A straight pure carrier covers at most one open side, hence `p>=4`.
This is a premise justified by that coverage theorem, not a conclusion
of local zero-loss tiling. Its exact applicability must be checked when
formalizing this stronger branch.

Every pure or shallow carrier is wholly in the annulus and remains a
distinct induced annulus component. Consequently `r_A>=p+h`.
Equations (10)--(11) now strengthen the physical-rank estimate to

```text
2K>=d+r_A+5>=d+p+h+5=r+5.                          (14)
```

Also `K<=b` without a coverage premise. Indeed outer boundary deficiency
over preserved vertices is `B+C_o`, so `b=4n-B-C_o`, and
`K=b+C_o-4-E<=b`.

For clarity, derive the stable numerical inequality from the
exact mass and ledger rather than estimating `r` twice. By (13),

```text
d=e+Q+K-6.
```

Substitute this and `r=p+h+d` in `3e+r+b+c=3Q+15` to obtain

```text
4e+p+h+K+b+c=2Q+21.
```

Since `b>=K`, this implies

```text
4e+p+h+2K+c<=2Q+21.                                (15)
```

Meanwhile (14) and the exact expression for `d` imply

```text
2K>=p+h+e+Q+K-1,
K>=p+h+e+Q-1.
```

Use twice this lower bound for `K` on the left side of (15), then cancel
`2Q`, to get precisely

```text
6e+3p+3h+c<=23.                                    (16)
```

With `p>=4`, `h>=0`, and `c>=1`, (16) gives `6e<=10`, hence `e<=1`.
The branch `e<=0` needs no argument, and the empty-annulus branch was
already below `T`. Thus the stronger paper result is `f<=T+1` for
`k>=5, Lambda=0`, using the preceding geometric proof and the stated
coverage input. This remains distinct from a formal Lean theorem.

## Reviewed Obligations

The read-only reviews checked the geometric classification and the full
contact/rank argument, including (9), (10), and the stronger consequence.
The following obligations must still be preserved in any revision or
formalization; neither the local packing identity nor the separate endpoint
strip theorem replaces them.

- Fourth-step endpoints: enumerate the assigned rows at each omitted step,
  including residues zero and one and the final inclusion into `E_N=empty`;
  check that (3) uses no unassigned distant row or invalid vertical step.
- Active phase: verify the adjacent-row consecutive-union obstruction,
  exact endpoint residues, the adjacent-axis cycle at every band interface,
  and the monotone birth/death conclusion in the one-orientation and
  point-intersection cases. Inactive saturation alone is not this proof.
- Bad edges: check each extreme side against the actual first/last band,
  including an active interval touching the deep boundary and an inactive
  endpoint free column. The component count depends on actual `BAD=0`.
- Singleton bound: exhaust the preserved-vertex possibilities in the four
  rows of each band, especially interval endpoints, shared outer rows, and
  annulus-extending singleton intersections. Check the six-/eight-cycle
  perimeter edges at corridor endpoints and at `p_U=0,Q`, not just the
  cardinality formula for three-spaced points.
- Contacts: verify that every birth/death reaches the claimed actual bar,
  that every gap column is absent from all occurring axis sets, and that
  the connector interiors are holes outside all retained components.
  Check all pairwise contact types, including singleton targets at core
  endpoints, boundary contacts, and the `L=Q` and `m=0` cases. The required
  conclusion is `2d` distinct physical paths with disjoint interiors, not
  a virtual incidence diagram or two labels on one path.
- Rank and annulus: retain all annulus isolates and actual induced deep
  trees; justify contraction/suppression without introducing an unforced
  edge. Check the corner signs in (11), and distinguish `r_A`, `r`, and
  the auxiliary mirror-path component counts.
- Stronger branch: confirm the hypotheses and meaning of the existing
  `k>=5` counterexample coverage theorem, `p>=4`, and `r_A>=p+h` before
  applying (14). The algebra (13)--(16) then uses signed integers and
  contains no additional packing or coverage assumption.

The reviews used source reading and mathematical analysis only. No searches,
builds, Lean changes, or computational experiments accompany this proof.
Positive `Lambda` may break phase rigidity, core counts, and contact
disjointness; none of those failures is bounded here. The general upper
problem and the constant-gap lower problem remain separate.
