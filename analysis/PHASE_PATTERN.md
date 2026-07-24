# Residue-Zero Phase Construction

This note records the exact construction implemented by
`residue_zero_phase_pattern(3k)` for `k >= 7` and the proof obligations needed
to turn it into the residue-zero lower-bound theorem.

## Phase Rows

Let `n = 3k`. For `0 <= a < k`, define ordinary row `R_a` and seam row `S_a`
by their dot columns:

```text
dots(R_a) = {3i : 0 <= i <= a}
          ∪ {3i+2 : a+1 <= i <= k-1}

dots(S_a) = {3i : 0 <= i <= a}
          ∪ {3i+2 : a <= i <= k-1}.
```

Thus `S_a` differs from `R_a` only by deleting the U vertex at column
`3a+2`. The two progressions are disjoint, so

```text
|R_a ∩ U| = 2k,
|S_a ∩ U| = 2k-1.
```

The seam row is the one-cell correction that absorbs one unit of the old
scaffold surplus.

## Interior Word

The `k=7` base word is

```text
B_7 = R4 R3 R2 S2 R1 R0 S0 R0 S1 R1 R2 S3 R3 S4 R4 R5 R6.
```

For `k >= 7`, interpret every row at the current width `3(k+1)` and set

```text
B_(k+1) = R_(k-2) S_(k-2) B_k R_k.
```

The complete pattern is

```text
empty row
all-U row
B_k
.U^(3k-1)
.U.^(3k-2)
```

The base has 12 ordinary and 5 seam rows. Every extension adds two ordinary
rows and one seam row. Therefore `B_k` has

```text
2k-2 ordinary rows,
k-2 seam rows,
3k-4 rows in total.
```

## Cardinality

The interior contributes

```text
(2k-2)(2k) + (k-2)(2k-1) = 6k^2 - 9k + 2.
```

The four cap rows contribute

```text
0 + 3k + (3k-1) + 1 = 6k.
```

Hence

```text
|U| = 6k^2 - 3k + 2 = q(3k),
|F| = 3k^2 + 3k - 2.
```

This part is a direct algebraic proof for every `k >= 7`.

## Dual Edge Count

A horizontal primal U-U edge gives a vertical dual edge; a vertical primal
U-U edge gives a horizontal dual edge. In a phase row,

```text
horizontal U-U edges in S_a:       k-1,
horizontal U-U edges in R_a:       k+1  if a < k-1,
horizontal U-U edges in R_(k-1):   k.
```

Every adjacent pair internal to `B_k` has `2k-1` common U columns. The cap
transitions contribute `2k`, `2k`, and `1` common U columns. Summing gives

```text
horizontal primal U-U edges = 3k^2 + 3k - 4,
vertical primal U-U edges   = 6k^2 - 9k + 6,
total dual edges            = 9k^2 - 6k + 2.
```

The square grid has `(3k-1)^2` bounded faces, so the dual including OUT has

```text
1 + (3k-1)^2 = 9k^2 - 6k + 2
```

vertices. Once dual connectivity is proved, equality of edge and vertex counts
shows that the dual is unicyclic.

## Connectivity Invariant

Process phase rows from top to bottom. Use this frontier invariant:

> Every processed dual component not containing OUT meets the current bottom
> face row. No component has been sealed above the frontier.

The `B_7` base is a finite certificate over 20 frontier positions. Its adjacent
row transitions are exactly

```text
R_a R_(a-1), R_a R_(a+1), R_a S_a,
R_a S_(a+1), S_a R_(a-1), S_a R_a.
```

For the induction step, widening from `3k` to `3k+3` appends the periodic
right slab to the old rows and changes the word by

```text
B_(k+1) = R_(k-2) S_(k-2) B_k R_k.
```

Away from the seam, the new slab is a translated periodic dual ladder. At a
seam, deleting the U at `3a+2` can split a frontier interval, but the common-U
columns on both sides carry both pieces into the next row. The only local words
that need checking, up to translation and reflection, are the six transitions
listed above. The final dense cap joins all surviving frontier components and
uses the right boundary to attach them to OUT.

This reduces connectivity for all `k` to the finite `B_7` base and a fixed
transition table. `check_diagonal_patterns.py` currently executes the full
graph check; formalizing the finite frontier certificate remains the main
construction-side proof task.

## From Dual To Tree

Let `F` be the complement of `U`. The forced graph contains exactly the primal
grid edges that are not U-U edges. For a connected plane graph, connectivity of
the complementary dual edges implies that this forced graph is acyclic.

Once acyclicity is available, Lean theorem
`SimpleGraph.isAcyclic_extends_to_isTree` extends the forced graph to a spanning
tree. `GridGraphs.exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic` packages
this step and proves that every vertex of `F` preserves all incident grid edges.

The substantial missing Lean result is therefore the grid-specialized planar
dual implication, followed by formal definitions of `R_a`, `S_a`, and `B_k` and
the finite frontier certificate.

## Verification

The generated base is exactly the cached stochastic witness:

```text
residue_zero_phase_pattern(21) == residue_zero_explicit_pattern(21).
```

The end-to-end checker has passed every supported multiple of three through
`n=120`; separate stress checks passed through `n=300`. Representative dual
metrics are connected with cycle excess one. These are candidate-construction
checks, not exact optimization runs.
