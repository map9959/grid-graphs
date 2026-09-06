# Residue-Two Affine Rooted Interval Skeleton Baseline

## Scope

This note is the lower L1 baseline extracted from the existing affine family.
It specifies a deterministic rooted tree of straight preserved intervals and
its `k -> k+1` transition for `n=3k+2`. It is potential input to an L2 tree
surgery design. It is **not** a target-count skeleton: its preserved score is
`3k^2+6k+5`, while the required stable score is `3k^2+7k`.

The executable export is produced by
`analysis/residue_geometry/check_residue_two_affine_interval_skeleton.py`. The checked artifact
`analysis/residue_two_affine_rooted_interval_skeleton.json` contains the full
nodes, parent map, physical parent attachments, old-node embeddings, and
transitions for `k=7,8,9`.

## Canonical Node Data

A straight component is named by orientation, fixed coordinate, and inclusive
moving-coordinate endpoints:

```text
H:rR:cA..B
V:cC:rA..B
```

Its length is `B-A+1`. Nodes are ordered lexicographically by the tuple
`(orientation, fixed, A, B)`, with `H < V`. The first node is the canonical
root. For the affine family this is

```text
H:r0:c2..(3k+1),
```

of length `3k`. Breadth-first traversal from that root, visiting adjacent nodes
in node order, defines the parent map. The physical parent attachment of a
nonroot interval is the unique grid vertex shared by its forced star and its
parent's forced star. Children are ordered by node order and carry the same
physical attachment. Consequently the export contains all L1 fields:
orientation, fixed coordinate, endpoints, parent attachment, and ordered child
attachments.

For each checked width there are `4k` nodes and `4k-1` singleton physical
attachments. The attachment graph is connected and hence a tree. Every
interval-star is acyclic, and the existing deterministic leaf elimination also
succeeds.

## Affine Insertion

The successor duplicates three source rows and columns:

```text
rows:    0..8, 9,10,11, 9..n-1
columns: 0..3, 4,5,6, 4..n-1.
```

The standard old-coordinate image is

```text
(r,c) -> (r + 3*[r>=9], c + 3*[c>=4]).
```

Because source rows `9,10,11` and columns `4,5,6` occur twice, this coordinate
map is not the whole ownership definition. For each old interval, list all
successor intervals containing an occurrence of every old vertex. Choose the
candidate with maximum overlap with the standard image, breaking ties by node
order. Within the chosen interval, an old vertex is represented by its
lexicographically first occurrence. This gives a deterministic injective map
of all `4k` old nodes and their vertices.

The ownership relation before the tie-break is genuinely nonunique. At every
checked step exactly three old intervals have two possible successor owners:

```text
H:r2:c5..5,
V:c6:r4..(3k-1),
V:c(3k-6):r10..11.
```

They lie on duplicated columns or rows. The JSON records both candidates and
the chosen owner. Thus the affine transition is deterministic after the stated
rule, but it is not a globally uniform one-occurrence affine embedding. Any L2
surgery that depends on unique raw ownership must address this seam behavior.

## Rooted Transition

Under the canonical ownership rule:

```text
old embedded nodes                 4k
old parent changes                   0
physical parent attachment mismatches 0
new nodes                             4
```

The four new nodes in the `k -> k+1` successor are

```text
H:r2:c5..5                         length 1
H:r12:c(3k-1)..(3k-1)             length 1
V:c6:r4..(3k+2)                   length 3k-1
V:c(3k-3):r10..11                 length 2.
```

All four are leaves in the canonical rooted successor. Their parent and exact
physical parent vertex are width-dependent and are exported directly. In
closed form they attach as follows:

```text
H:r2:c5..5
  parent H:r0:c2..(3k+4), attachment (1,5)

H:r12:c(3k-1)..(3k-1)
  parent V:c(3k+1):r9..(3k-1), attachment (12,3k)

V:c6:r4..(3k+2)
  parent H:r(3k+4):c2..(3k+2), attachment (3k+3,6)

V:c(3k-3):r10..11
  parent V:c(3k-3):r13..14, attachment (12,3k-3).
```

No old branch is detached or reparented in the affine baseline. This is useful
control data for surgery, not the surgery required by L2.

## Exact Length Recurrence

Exactly `k+2` old intervals lengthen, each by three. They consist of four outer
spines/caps, `k-4` repeated vertical intervals, one moving vertical interval,
and the bottom horizontal interval. Therefore

```text
H:r0:c2..(3k+1)
  -> H:r0:c2..(3k+4)

H:r(3k+1):c2..(3k-1)
  -> H:r(3k+4):c2..(3k+2)

V:c0:r0..(3k+1)
  -> V:c0:r0..(3k+4)

V:c3:r3..(3k-1)
  -> V:c3:r3..(3k+2)

V:c(3j):r4..(3k-1)
  -> V:c(3j+3):r4..(3k+2),  2 <= j <= k-3

V:c(3k-2):r9..(3k-4)
  -> V:c(3k+1):r9..(3k-1)

V:c(3k+1):r3..(3k+1)
  -> V:c(3k+4):r3..(3k+4).
```

The indexed vertical family contributes `k-4` nodes; the other six displayed
nodes give `(k-4)+6=k+2`. Therefore

```text
old-node length gain = 3(k+2) = 3k+6.
```

The four new lengths sum to

```text
1 + 1 + (3k-1) + 2 = 3k+3.
```

Hence the exact affine recurrence is

```text
(3k+6) + (3k+3) = 6k+9,

(3(k+1)^2 + 6(k+1) + 5) - (3k^2 + 6k + 5)
  = 6k+9.
```

The target recurrence is instead

```text
(3(k+1)^2 + 7(k+1)) - (3k^2 + 7k) = 6k+10.
```

Thus the rooted affine interface transports without a parent or physical
attachment mismatch, but its cardinality interface has exact mismatch

```text
(6k+9) - (6k+10) = -1.
```

This one-vertex deficit is the L2 design requirement. It cannot be removed by
calling the affine baseline a target skeleton.

## Verification And Limits

Focused tests replay transitions `7->8`, `8->9`, and `9->10`. They check the
node formulas, canonical root, injective old ownership, all transported parent
attachments, four new leaves, `k+2` changed lengths, gain `6k+9`, target gain
`6k+10`, and mismatch `-1`.

The formulas above are exact algebraic descriptions of the audited affine
descriptors. The executable checks at three widths guard the implementation;
they are not a proof that an unknown target skeleton exists. No target parent
map, target physical realization, branch surgery, or arbitrary-width
target-connectivity claim is made here.
