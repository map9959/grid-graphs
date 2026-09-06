# Residue-Two Counter-Interval Surgery

## Superseded Realization Status: 2026-09-05

The abstract tree and length identities below remain valid, but this is no
longer a viable uniform grid-realization candidate. The exact forced-forest
ledger and the corner/perimeter bound `boundaryDeficiency(U)>=5` imply that
a set of size `3k^2+7k` has at most `3k+6` maximal preserved components.
The proposed `4k+1` distinct components violate this throughout the intended
`k>=7` range. At k=7 it demands 29 components where at most 27 are possible.
Merging labeled intervals changes the proposed skeleton. See
`RESIDUE_TWO_COMPONENT_BUDGET.md` for the proof and qualifications. The general
obstruction is now checked in `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean` as
`not_feasible_target_of_four_mul_add_one_le_components`. Applying it to this
abstract skeleton still requires its nodes to be distinct maximal components.

## Result

For every `k>=7`, let `A_k` be the audited affine rooted interval tree.  Write

```text
R_k = H:r0:c2..(3k+1),
B_k = V:c0:r0..(3k+1).
```

The affine parent map has `parent(B_k)=R_k`, with physical owner `(0,1)`, and
the checked affine insertion maps `R_k` and `B_k` to `R_(k+1)` and `B_(k+1)`.
Define the abstract surgery `S_k` by deleting this parent edge, introducing one
horizontal counter interval `C_k` of length `k-5`, and replacing the edge by

```text
R_k -> C_k -> B_k.
```

Thus the whole branch rooted at `B_k` is detached from `R_k` and reparented to
`C_k`.  Give `C_k` abstract local endpoints `0..k-6`.  Its fixed grid row is
not assigned at L2.  The two new singleton attachment owners are named
`alpha_k` for `R_k -> C_k` and `beta_k` for `C_k -> B_k`; they are distinct
symbolic owners and explicit L3 realization obligations.

## Exact Formulas

The index type and length are

```text
Node(S_k) = Node(A_k) + {C_k},
|Node(S_k)| = 4k+1,
|Edge(S_k)| = 4k,
length(C_k) = k-5,
length(S_k) = (3k^2+6k+5)+(k-5) = 3k^2+7k.
```

The insertion map is the affine old-node map together with

```text
C_k -> C_(k+1),
i -> i                  for 0 <= i <= k-6,
new endpoint = k-5.
```

All affine parent equations still commute.  The only modified equations also
commute exactly:

```text
parent(C_k) = R_k       -> parent(C_(k+1)) = R_(k+1),
parent(B_k) = C_k       -> parent(B_(k+1)) = C_(k+1).
```

The affine step lengthens `k+2` old intervals by three and introduces four
leaves of total length `3k+3`.  The counter contributes one new endpoint, so

```text
3(k+2) + (3k+3) + 1 = 6k+10.
```

This is one more than the affine gain and gives the target recurrence exactly.

## Tree And Elimination

Subdividing one edge of a tree preserves connectedness and acyclicity.  More
explicitly, retain every affine parent except the displayed override.  Every
nonroot node then has exactly one parent, and repeated parent iteration reaches
`R_k`: the affine argument applies except that the former step `B_k -> R_k` is
now `B_k -> C_k -> R_k`.

A uniform leaf-elimination order is postorder traversal of this parent map,
with children ordered by interval identifier.  At removal, all children have
already been removed, so a node meets the uneliminated suffix only through its
parent; the root meets it in zero nodes.  This transports through insertion.
Equivalently, insert each of the four new affine leaves before its parent in the
transported old postorder.  `C_k` is an old node under the surgery insertion,
and its position between the `B_k` branch and `R_k` is unchanged.

## Verification And Blocker

`analysis/check_residue_two_counter_interval_surgery.py` checks the exact
parent override, symbolic attachment-owner uniqueness, cardinality, transition,
and postorder elimination.  Its JSON artifact audits `k=7,8,9`; tests also run
at `k=12` to guard against fitting only the three artifact widths.

This is a credible L2 abstract surgery, not an L3 construction.  The unresolved
geometric specification is sharp:

1. Realize a horizontal interval `C_k` of length `k-5` in the grid.
2. Destroy the old root/branch star intersection at `(0,1)`.
3. Realize distinct singleton star intersections `alpha_k` and `beta_k`.
4. Introduce no other star intersections, preserved diagonal pair, three-center
   cell, or forced-star cycle.

Until those four obligations have coordinate formulas, the artifact must not
be read as a residue-two preserved-set candidate or a completed L3 gate.
