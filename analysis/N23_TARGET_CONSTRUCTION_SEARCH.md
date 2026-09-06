# N23 Target Construction Search

## Result

No 333-U witness was found in the finite neighborhoods below.  The machine-readable
certificate is `analysis/n23_target_search_result.json`; it is reproduced by
`python3 -m analysis.searches.n23_target_search` and checked by
`python3 -m unittest n23_target_search_test.py` from `analysis/`.

This is not a global nonexistence result for n=23.

## Sources

The connected source is `diagonal_patterns.residue_two_affine_pattern(23)`, the
affine `A23` control obtained by the established row/column duplication recurrence.
It has:

- 335 U vertices;
- SHA-256 `c8e49712aa353cd61057b83aeb532c23d3380542b46785dfee1f26d462871cb1`;
- all 485 dual faces connected to OUT; and
- a forest-completable forced graph.

The second source is `residue_two_revised_recurrence.target_charge_candidate(7)`,
the uniform-right symbolic target-charge probe.  It has exactly 333 U vertices,
SHA-256 `1f6fd619cba3c993bd9e61f59b39c137b23350ce3e318e2bd226c1903246bdff`,
and is not a witness: its dual has eight components (OUT reaches 64 of 485 faces)
and its forced graph contains a cycle.

Hashes encode the 23 ASCII rows joined by LF, including one trailing LF.

## Affine Deletions

Every unordered pair of the 335 source U cells was materialized and passed through
`construction_lab.dual_connectivity_check`:

| Search | Generated | Dual-connected | Forest-completable |
|---|---:|---:|---:|
| remove 2, add 0 | 55,945 | 0 | 0 |

Thus no pure two-U deletion of affine `A23` reaches a valid 333-U pattern.

## Affine Seam Halo

The affine recurrence duplicates zero-based rows 9..11 and columns 4..6.  The
bounded search window is their radius-two rectangular halo, rows 7..13 and columns
2..8 inclusive.  It contains 49 cells: 35 source U cells and 14 dots.

Both balanced net-minus-two orders were exhaustive in this window:

| Search | Addition sets | Unpruned exchanges | Exact survivors | Hits |
|---|---:|---:|---:|---:|
| remove 3, add 1 | 14 | 91,630 | 0 | 0 |
| remove 4, add 2 | 91 | 4,764,760 | 0 | 0 |

The pruning is exact.  If deleting a set `S` from an augmented connected dual
leaves it connected, restoring all but one deleted cell cannot destroy
connectivity.  Consequently every member of `S` must be individually removable
after the additions.  Each of the 14 one-addition and 91 two-addition augmentations
had zero individually removable source U cells in the window, excluding every
listed removal tuple without a lossy heuristic.

## Symbolic Swaps

The symbolic step inserts rows 8..10 and appends a packet in columns 20..22.  Its
bounded seam neighborhood is the cross consisting of rows 6..12 union columns
18..22, all bounds inclusive.  The 241-cell cross contains 152 U cells and 89 dots.

| Search | Addition sets | Connected after additions | Unpruned swaps | Hits |
|---|---:|---:|---:|---:|
| remove 1, add 1 | 89 | 0 | 13,528 | 0 |
| remove 2, add 2 | 3,916 | 0 | 44,940,016 | 0 |

This prune is also exact: changing U to dot only removes dual edges.  Since no
allowed addition set connects the symbolic baseline, subsequent balanced removals
cannot connect it.  No removal tuple therefore needs canonical replay.

## Scope And N26

The exact negative result covers only:

- all pure two-U deletions from this affine `A23` orientation;
- remove-3/add-1 and remove-4/add-2 exchanges wholly inside the stated affine
  7x7 seam halo; and
- one-for-one and two-for-two swaps wholly inside the stated symbolic seam cross.

It does not cover larger exchanges, other spatial windows, D4-mixed caps, global
phase changes, or arbitrary 333-U patterns.  Because no n23 witness was found,
there is no valid open-slab signature to test for composition to n26; the result
artifact records `not_run_no_n23_witness` rather than making a composition claim.
