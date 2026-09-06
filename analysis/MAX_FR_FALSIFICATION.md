# Max-FR computational falsification gate

This is finite computational evidence only. It is not a Lean proof claim.

`max_fr_checker.py` mirrors the four corner embeddings from
`FourCropSurgery.lean`: an `(n-3) x (n-3)` block is embedded at row and column
offsets independently chosen from `0` and `3`. Frame loss is the number of
ambient forced vertices outside that block.

For each crop, the checker computes the actual bundled repair rank `rho`
exactly. It maximizes the number of initially unforced crop vertices that can
be forced simultaneously while the complete resulting forced-edge graph stays
acyclic. Thus adjacent selected vertices share one physical edge, and every
edge incident to a selected vertex is inserted; omitted edges are not treated
as individually selectable.

## Results: two distinct conjectures

The proposed maximum-only sum inequality (Max-FR) is false at `n=9`. One maximum
forced-acyclic set, as little-endian row masks, is

```text
509, 1, 65, 285, 257, 353, 265, 257, 381
```

It has 34 vertices, matching the exact `n=9` value in `data/diagonal.csv`.
The independent direct checker confirms forced acyclicity. In corner order
`NW, NE, SW, SE`, its losses, positive demands, and exact repair ranks are

```text
loss: 20, 20, 19, 19
demand = max(0, loss - 18): 2, 2, 1, 1
rho: 1, 1, 1, 1
```

Consequently

```text
sum rho = 4 < 6 = sum(loss - 2n).
```

The stronger positive-demand version fails by the same margin. A balanced
crop still exists: both southern crops have `rho = loss - 2n = 1`.

The regression test independently replays each rank-one upper bound by trying
every pair of eligible repair vertices in the direct forced-acyclicity checker;
every pair is cyclic, while at least one singleton is acyclic.

This failure does not by itself refute the weaker direct balanced-crop
conjecture

```text
some Q has rho(Q) >= max(0, loss(Q)-2n).
```

Indeed, the displayed Max-FR counterexample has two balanced crops. The
campaign therefore tracks `max_fr_counterexample` and
`balanced_crop_counterexample` separately and does not stop after finding the
former.

The expanded balance-targeted search subsequently found that the direct
balanced-crop conjecture is also false at `n=9`. A maximum witness is

```text
509, 1, 65, 285, 257, 369, 261, 1, 505
```

All four corner crops have frame loss `19`, demand `19-18=1`, and exact repair
rank zero. Thus no minimum-loss crop is balanced and no crop is balanced. The
full set has size `34`, the independent direct checker confirms its forced
graph is acyclic, and the rank-zero regression independently tries every
eligible singleton repair in every crop; all are cyclic. This is a stronger
negative result than the original Max-FR counterexample and changes the
formerly surviving balanced-crop conjecture's status.

## Coverage

The exhaustive optimal-witness generator enumerated every maximum forced set
for `n=3..6`, with counts `24, 14, 242, 96`. No balanced-crop failure occurred
there. (`n<3` is outside the four-crop embedding's domain.) The expanded run
then checked targeted dihedral images, three retained exact `n=9` witnesses,
cardinality-preserving random exchanges, and exchanges biased toward minimizing
the best crop's balance margin. In one reproducible run it checked `10, 125,
49` distinct exact maximum witnesses for `n=7,8,9` respectively.

For every checked witness the JSON result records `min_corner_frame_loss`,
`min_loss_minus_2n`, `minimum_repair_rank_needed`,
`minimum_loss_crop_balanced`, and `some_crop_balanced`. Each per-`n` record
reports distributions of the numeric values and true/false distributions of
the two balance predicates. The reproducible run above gives:

| `n` | coverage | checked | min loss distribution | min loss minus `2n` | repair rank needed | minimum-loss crop balanced | some crop balanced |
|---:|:---|---:|:---|:---|:---|:---|:---|
| 3 | exhaustive | 24 | `4:24` | `-2:24` | `0:24` | yes: 24 | yes: 24 |
| 4 | exhaustive | 14 | `7:14` | `-1:14` | `0:14` | yes: 14 | yes: 14 |
| 5 | exhaustive | 242 | `9:242` | `-1:242` | `0:242` | yes: 242 | yes: 242 |
| 6 | exhaustive | 96 | `12:96` | `0:96` | `0:96` | yes: 96 | yes: 96 |
| 7 | targeted/random | 10 | `14:10` | `0:10` | `0:10` | yes: 10 | yes: 10 |
| 8 | targeted/random | 125 | `17:125` | `1:125` | `1:125` | yes: 125 | yes: 125 |
| 9 | targeted/random | 49 | `19:49` | `1:49` | `1:49` | yes: 35, no: 14 | yes: 35, no: 14 |

Run:

```bash
python3 -m unittest discover -s analysis -p 'test_max_fr_checker.py'
python3 -m analysis.bounds.max_fr_checker --exhaustive-max-n 6 --exhaustive-limit 100000000
```

The campaign exits nonzero only for a balanced-crop counterexample. A Max-FR
counterexample is reported but does not truncate the weaker-property search.
