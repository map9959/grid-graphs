# Bundle cycle defect census

This is finite exact computational evidence, not a proof for uncomputed grids.

## Statistics and identities

Let `F` be forced-acyclic, `U=V\F`, and let `H` contain every grid edge with
at least one endpoint in `F`. For every `u in U`, the checker computes the Lean
definitions `bundleCycleDefect H F u` and `starAttachmentGraphicRank H F u`
from the exact `H`-component labels. Write their sums as `D` and `R`, and write
`B_U` for the boundary deficiency of `U`.

Every profile independently replays

```text
D + R = 2|E(G[U])|,
3|F| + c(G[F]) + c(H) = n^2 + 4n - B_U,
n^2 + 3n - 4 - 3|F| = B_U + c(G[F]) + c(H) - n - 4.
```

Thus the first proposed use of `D+R` is only an identity, and the last line is
exactly equivalent to the desired bound rather than a new invariant.

## Surviving strengthening

The non-equivalent linear inequality surviving the complete census is

```text
B_U + c(G[F]) + c(H) >= n + 3 + c(G[U]).                 (CU)
```

For the maximal sets under consideration `U` is nonempty, so `c(G[U])>=1`.
Consequently (CU) implies

```text
3|F| + 4 <= n^2 + 3n.
```

It is genuinely stronger: its margin is the target margin minus
`c(G[U])-1`. The extra term matters on maximal, nonmaximum examples with two
unforced components. A proof of (CU), rather than another rearrangement of the
component identity, would therefore close the target.

## Component conventions

All three component counts use the full mathematical graphs named in (CU):

* `c(G[F])=0` when `F` is empty, and otherwise includes isolated `F` vertices;
* `c(G[U])=0` when `U` is empty, and otherwise includes isolated `U` vertices;
* `H` is spanning on all `n^2` grid vertices. In particular, a `U` vertex with
  no `F` neighbour is an isolated component of `H`.

The main checker obtains these values by disjoint sets. Every checked profile
now replays them independently with plain DFS component searches. A regression
pins the extreme convention `F=empty` on the `3 x 3` grid as
`(B_U,c(G[F]),c(G[U]),c(H))=(12,0,1,9)`. The conjecture is scoped to `n>=2`:
at the degenerate `n=1` all-forced set, (CU) is false.

## Exact coverage and distributions

Every forced-acyclic set, maximal or not, was exhausted with the exact row
grammar through `n=5`:

| `n` | all acyclic sets | minimum (CU) margin | equality sets |
|---:|---:|---:|---:|
| 2 | 9 | 0 | 4 |
| 3 | 100 | 2 | 0 |
| 4 | 2,278 | 0 | 14 |
| 5 | 116,252 | 3 | 0 |

Thus the complete small census is stronger than the maximal-set census below.
The unit test itself traverses all 116,252 `n=5` sets and checks every margin.

All inclusion-maximal forced forests were exhausted through `n=5`:

| `n` | maximal sets | `|F|` distribution | target margin distribution | (CU) margin distribution | `c(G[U])` |
|---:|---:|:---|:---|:---|:---|
| 2 | 4 | `2:4` | `0:4` | `0:4` | `1:4` |
| 3 | 26 | `3:2, 4:24` | `5:2, 2:24` | `4:2, 2:24` | `1:24, 2:2` |
| 4 | 138 | `5:32, 6:76, 7:16, 8:14` | `9:32, 6:76, 3:16, 0:14` | `9:24, 8:8, 6:72, 5:4, 3:16, 0:14` | `1:126, 2:12` |
| 5 | 2164 | `7:14, 8:332, 9:752, 10:824, 11:242` | `15:14, 12:332, 9:752, 6:824, 3:242` | target margin except 76 two-component cases lose one | `1:2088, 2:76` |

Every maximum set was exhausted through `n=8`, with counts
`4,24,14,242,96,16,704` for `n=2..8`. Their target margins are respectively
`0,2,0,3,2,0,3`; every one has connected `G[U]`, so the (CU) margins are the
same. The checker additionally covers targeted certified maximum witnesses at
`n=9..12,14,15`. Their (CU) margins are `2,0,3,2,3,2`. The canonical `n=13`
construction also has margin zero, but its maximum status is not certified in
`data/diagonal.csv`.

## Adversarial extension through `n=15`

For each `n=6..15`, the checker starts with canonical/targeted witnesses, builds
random maximal sets by greedy exact-row-grammar extension, and repeatedly
removes one to three forced vertices before randomly re-maximalizing. It accepts
all non-worsening moves for the (CU) margin plus a small escape probability.
Every retained set is checked both by the row grammar and by the independent
direct cycle checker; maximality is then checked from the exact defect profile.

A reproducible 64-attempt-per-width run retained respectively
`27,17,24,19,30,14,13,11,12,11` distinct maximal witnesses. Its minimum margins
for `n=6..15` were

```text
2, 0, 3, 2, 0, 3, 2, 0, 3, 2.
```

No negative margin was found. These values are finite observations, but expose
a stable period-three minimum: equality at sampled widths `n=7,10,13`, margin
three at `n=8,11,14`, and margin two at `n=6,9,12,15`.

## Equality structures

In the complete `n<=5` census, equality occurs only among maximum sets: all four
maximum `n=2` sets and all fourteen maximum `n=4` sets. Their profiles
`(|F|,B_U,c(G[F]),c(G[U]),c(H))` are

```text
n=2: (2,4,1,1,1)                    [4 sets]
n=4: (8,4,3,1,1)                   [12 sets]
     (8,4,2,1,2)                    [2 sets]
```

All sixteen exact maximum sets at `n=7` are also equality sets, all with profile
`(22,6,4,1,1)`. The sampled `n=10,13` equalities continue to have connected
`G[U]`; no equality with the extra credit `c(G[U])-1>0` was found. The report
now records the full equality-profile distribution and a first minimum-margin
witness for every coverage class.

The JSON report records full distributions of `D`, `R`, `B_U`, all three
component counts, the per-vertex defect histogram, both margins, and equality
counts for every `n` and coverage class.

## Failed stronger credits

The script tests whether any of the following nonnegative quantities can be
subtracted from the target margin. Only `c(G[U])-1` survives.

| attempted extra credit | first failure |
|:---|:---|
| `D-|U|` | `n=3`, rows `FUU/UUF/FUF`: target margin `2`, credit `3` |
| `R` | `n=3`, rows `FUU/UUU/FFF`: target margin `2`, credit `3` |
| `c(G[F])-1` | `n=4`, rows `FUUF/FUUF/UUUU/FFFF`: target margin `0`, credit `2` |
| `c(H)-1` | `n=4`, rows `FUUF/FUUF/FUUF/FUUF`: target margin `0`, credit `1` |

These examples are inclusion-maximal, not arbitrary acyclic sets. In
particular, maximality gives the local fact `defect(u)>=1` and hence `D>=|U|`,
but the first counterexample shows that its total surplus cannot simply be
charged against the desired global margin.

Run:

```bash
python3 -m unittest discover -s analysis -p 'test_bundle_cycle_defect_census.py'
python3 analysis/bundle_cycle_defect_census.py
```
