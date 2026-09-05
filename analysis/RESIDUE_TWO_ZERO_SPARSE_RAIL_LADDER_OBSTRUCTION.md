# Phase-Alternating Twelve-Site Sparse-Rail Ladder

## Exact Grammar

Continue the double-cap exchange with `m=3k`, `n=m+2`.  There are `k-2`
interior packets starting at coordinate `2+3t`.  Each arm has six declared
sites:

```text
three outer-rail candidates,
two old-cap-layer reservoir/rung sites complementary to the rail gap,
one new-inner-layer connector at the rail gap.
```

Thus each two-arm packet has twelve sites.  Select ten:

```text
2 outer + 2 old-layer + 1 connector = 5 per arm.
```

For initial phase `p` and direction `d in {-1,+1}`, packet `t` uses

```text
gap(t) = p + d*t mod 3.
```

The outer and old-layer masks omit `gap(t)`; the connector occupies it.  This
is the declared complementary singleton mask.  With one of the four existing
sixteen-vertex caps,

```text
10(k-2)+16 = 10k-4.
```

The complete descriptor bound is

```text
4 orientations x 3 bottom phases x 3 right phases
x 2 bottom directions x 2 right directions x 4 cap masks = 576.
```

All descriptors are materialized; there is no cutoff or open search.

## Checked Gates

Every descriptor at `k=7,8,9` has:

- replacement count `10k-4`;
- target forced count `3k^2+7k`;
- valid unit cells;
- only straight forced components; and
- exact count gain ten under one additional three-column packet.

No descriptor has singleton star intersections, a tree incidence graph, or an
acyclic forced graph.

| `k` | `n` | descriptors | minimum star intersection | minimum cycle rank | survivors |
|---:|---:|---:|---:|---:|---:|
| 7 | 23 | 576 | 3 | 40 | 0 |
| 8 | 26 | 576 | 3 | 50 | 0 |
| 9 | 29 | 576 | 3 | 58 | 0 |

## Exact Obstruction

Sparse rails remove two forced vertices per packet, but exact gain ten puts
three compensating auxiliary vertices per arm onto only two inner tracks.  The
old-layer mask is parallel to the outer complementary mask.  Phase cycling
changes where their runs begin, but cannot remove all common runs.  The gap
connector then supplies a third competing star attachment.  For `k>=7`, every
phase and direction has a pair of interval stars sharing at least three
physical support vertices.

The cardinality recurrence is stable, but the incidence-parent interface is
not.

## Branch Decision

The fixed two-layer residue-zero neighboring-cap splice is no longer justified.
Three successively enlarged exact grammars fail for the same density reason:

```text
outer fixed hub:       capacity short by k-3,
saturated two-layer:   parallel intersection 3k-5,
double-cap ten-site:   minimum intersection 2,
sparse twelve-site:    minimum intersection 3.
```

Adding bounded reservoir leaves only transfers the collision between the two
available tracks.  A further attempt is justified only after a structural
relaxation: either a genuine three-layer moving seam or deletion of another old
interval.  Neither is a two-row/two-column neighboring-residue cap splice, so
this lower branch should stop here rather than enlarge the packet grammar again.
