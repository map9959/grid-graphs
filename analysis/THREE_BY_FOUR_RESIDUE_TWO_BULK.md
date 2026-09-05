# 3x4 Residue-Two Bulk Classification

## Scope

For `n=3k+2`, tile the `3k x 3k` interior by a `3x4` mask with four
preserved centers. The width-one cap uses the hard straight-interval grammar:
forced-star intersections are singletons and their incidence graph is a
forest. The classifier exhausts every mask and every translation/reflection
phase in this declared family.

## Bulk Census

There are `C(12,4)=495` density-one-third masks. Toroidal `2x2` constraints
leave 33. The voltage quotient then gives this complete ledger:

| quotient fundamental rank | count | result |
|---:|---:|---|
| 1 | 3 | survive |
| 2 | 12 | commutator obstruction |
| 3 | 12 | commutator obstruction |
| 5 | 6 | commutator obstruction |

The important point is that rational independence of cycle voltages is not the
forest criterion once the quotient rank is at least two. The quotient
fundamental group is free. Two generators have a nontrivial commutator, while
every commutator maps to zero in the abelian deck group `Z^2`; its lift is a
cycle. Thus a periodic lift is a forest exactly when each quotient component
has rank zero, or rank one with a nonzero generator voltage.

The 12 rank-two masks are the tempting crossed-rail patterns. Their two
fundamental voltages can be `(1,0)` and `(0,1)`, but a `6x8` open box already
contains the commutator cycle. They do not survive symbolically.

The three actual survivors are

```text
1111  0000  0000
0000  1111  0000
0000  0000  1111
```

They are one translation/reflection orbit: a complete row in one of three row
phases. Consequently the bulk is exactly `3k^2`. The period-four coordinate is
constant, so clipping at `3k` columns has no effect for any `k mod 4`:
`3k mod 4` runs through `0,3,2,1`, but all four classes have the same count.

## Hard Cap Grammar

The finite state is the row phase, endpoint choice, cap distance in `{1,2,3}`,
singleton gap counter in `{0,1,2}`, and four corner-ownership bits. Its hard
transitions are the same for all four `k mod 4` classes:

1. Each transverse side has at most `k` legal rail endpoints.
2. A distance-one parallel cap bends a component or closes a unit cell.
3. A distance-three cap is one disjoint full rail of length `3k+2`.
4. At distance two, cap components are singletons separated by at least three;
   the gap automaton gives `k+1`.
5. Corners are owned by the parallel cap and add no independent allowance.

Outer row phases attain

```text
2k + (3k+2) = 5k+2,
```

while the center phase attains `2k+2(k+1)=4k+2`. Hence the exact family maximum
is

```text
P(k) = 3k^2 + 5k + 2.
```

## Obstruction And Decision

Against `T(k)=3k^2+7k`, the exact deficit is `2k-2`. The one-step gains are
`P(k+1)-P(k)=6k+8` and `T(k+1)-T(k)=6k+10`. Across a full period-four phase,
they are `24k+68` and `24k+76`.

The materialized maxima are `184`, `234`, and `290` at `k=7,8,9`; the targets
are `196`, `248`, and `306`. Every witness passes the full forced-forest check.

No `3x4` family reaches the target. It adds no surviving topology beyond the
period-three rail, so the next periodic census should be `6x6`, the next square
density-one-third cell. Nonperiodic topology is the fallback only if the `6x6`
quotient and cap classification also fails.
