# Period-Three Residue-Two Bulk Classification

## Scope

Let `n=3k+2`. The bulk is the `3k x 3k` core on rows and columns
`1..3k`, tiled by a `3x3` preserved-center mask containing exactly three
centers. The outer width-one ring is a boundary cap. Boundary components are
required to be straight intervals; their forced stars have singleton
intersections and forest incidence. These are precisely the stated
period-three bulk families, not all possible residue-two constructions.

## Complete Bulk Census

The checker visits all 512 masks and filters the 84 masks of weight three. In
every translated `2x2` unit cell, three centers or a diagonal pair forces the
cell cycle. Only six masks pass:

```text
111  000  000       100  010  001
000  111  000   or  100  010  001
000  000  111       100  010  001
```

The right display denotes the three column phases, not diagonal masks. Thus
the survivors are exactly one complete row or one complete column, with three
phases each. Dihedral symmetry and translation put all six in one orbit.

For a periodic forced graph, choose a spanning forest of its nine-vertex
voltage quotient. If `beta=E-V+C`, each non-tree edge gives one cycle voltage
in `Z^2`. A finite cycle in the lift is exactly a nonzero integral cycle-space
element with zero voltage. Hence the lift is a forest exactly when the map
`Z^beta -> Z^2` is injective. Every survivor has `E=9`, `C=1`, `beta=1`, and a
nonzero rail-direction voltage. Open boxes with two through eight repetitions
are checked only as corroboration; the voltage criterion is the symbolic
arbitrary-repetition argument.

Every survivor therefore consists of parallel straight rails and contributes
exactly

```text
3 * (3k * 3k) / 9 = 3k^2
```

bulk centers.

## Boundary Grammar

Up to rotation there are three row phases. The finite cap state records the
rail endpoint choice, distance `1`, `2`, or `3` to the nearest parallel rail,
a gap counter in `{0,1,2}`, and corner ownership.

The hard transitions are:

1. A transverse boundary center away from a rail level has a two-vertex star
   intersection with an adjacent bulk rail, so it is forbidden. Each
   transverse side has at most `k` rail extensions.
2. A parallel cap at distance one either bends a preserved component or closes
   a unit cell, so it contributes zero.
3. At distance three, one full disjoint boundary rail is legal and has length
   `3k+2`.
4. At distance two, every cap component is a singleton. Two such sites less
   than three columns apart form a cycle through their common bulk rail. The
   three-state gap automaton therefore admits at most `k+1` sites.
5. A corner belongs to its parallel cap. Exhausting its two ownership bits
   adds no separate corner allowance.

Consequently the two outer phases have exact cap maximum

```text
2k + (3k+2) = 5k+2,
```

attained by extending every core rail and adding the distance-three boundary
rail. The centered phase has exact maximum

```text
2k + 2(k+1) = 4k+2,
```

attained by the rail extensions and singleton cap sites at columns `1 mod 3`.
The artifact materializes both maximizers and checks straightness and the full
forced forest at `k=7,8,9`.

## Obstruction

The best complete period-three family has

```text
P(k) = 3k^2 + 5k + 2.
```

It misses `3k^2+7k` by `2k-2`. Its stable increment is `6k+8`, while the
target increment is `6k+10`. Thus no period-three tiled bulk with the declared
straight-interval/forest-incidence boundary can attain the target.

The next density-compatible rectangular period is `3x4` (four centers), up to
rotation; the next square period is `6x6` (twelve centers). The local census
shows why a genuinely new topology is necessary: phase-staggered bent rails
or diagonal carriers must share one controlled articulation per packet rather
than remaining parallel disjoint stars.
