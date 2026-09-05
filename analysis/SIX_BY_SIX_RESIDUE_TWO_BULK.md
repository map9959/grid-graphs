# 6x6 Periodic Residue-Two Bulk Classification

## Row-State Census

For `n=3k+2`, the bulk is the `3k x 3k` core and a periodic `6x6` cell
contains twelve preserved centers. The classifier does not visit `2^36` masks,
or even the `C(36,12)=1,251,677,700` fixed-weight masks. Its states are the 64
six-bit row masks. A directed transition is legal exactly when every cyclic
`2x2` cell between its rows avoids three centers and avoids both diagonal
pairs. There are 324 transitions. Weight-pruned closed walks of length six and
total weight twelve give exactly 110,832 locally legal cells.

For each walk, the forced graph is represented as a 36-vertex voltage quotient.
The test is componentwise. A quotient component of free rank at least two is
rejected because a nontrivial commutator maps to zero in the abelian deck group
`Z^2`. Rank one survives exactly when its generator has nonzero voltage; rank
zero always survives. This is an arbitrary-lift criterion, unlike finite-box
sampling.

Exactly six cells survive:

```text
000000  000000  111111  000000  000000  111111
```

and its two other transverse translations, together with the three rotated
versions. Torus translations and square dihedral symmetry identify all six.
The primitive period is `3x1` for horizontal rails or `1x3` for vertical rails,
so the 6x6 census produces no topology beyond the period-three family. The
quotient has two components, each a rank-one rail carrying nonzero longitudinal
voltage. The `3k x 3k` core therefore has `3k^2` centers.

## Finite Boundary Grammar

Up to rotation, the state records the transverse phase in `{0,1,2}`, endpoint
extension, parallel-cap distance in `{1,2,3}`, singleton gap counter in
`{0,1,2}`, and corner ownership. A transverse side can extend its `k` rail
endpoints. A distance-one cap is forbidden. A distance-three cap is one full
rail of length `3k+2`. At distance two, cap sites are singletons and the finite
grammar

```text
occupied: 0 -> 2, weight 1
empty:    s -> max(0,s-1), weight 0
```

gives `k+1` sites along a side of length `3k+2`. Corners are owned by the
parallel cap and add no independent allowance. Thus the phase maxima are

```text
phase 0: 2k + 0 + (3k+2) = 5k+2
phase 1: 2k + (k+1) + (k+1) = 4k+2
phase 2: 2k + (3k+2) + 0 = 5k+2.
```

The exact family maximum is `P(k)=3k^2+5k+2`.

## Target Obstruction

The target `T(k)=3k^2+7k` exceeds the cap-grammar maximum by `2k-2`, positive
for every `k>=7`. The explicit phase-0 and phase-2 maximizers are parallel core
rails extended through both transverse sides, plus the one legal disjoint
boundary rail. Their incidence topology is a disjoint collection of path-like
forced-star components; no target construction survives.

The direct checks are:

| `k` | `n` | family maximum | target | deficit |
|---:|---:|---:|---:|---:|
| 7 | 23 | 184 | 196 | 12 |
| 8 | 26 | 234 | 248 | 14 |
| 9 | 29 | 290 | 306 | 16 |

All materialized phase maximizers pass the full finite-grid forced-forest test.
This exhausts density-one-third 6x6 periodic bulks, including every survivor of
smaller primitive period represented in a 6x6 cell. Together with the separate
3x3 and 3x4 classifications it exhausts the periodic families tested here, but
does not claim an obstruction for arbitrary larger periods or nonperiodic
bulks.
