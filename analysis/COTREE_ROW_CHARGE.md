# Cotree row charge census

This note records finite computational evidence, not a proof.  The terminology
is for a spanning tree `T` of the `n x n` grid, its cotree `C=G\\T`, and the
cotree support `S`.  Here `c_S` is the number of connected components of `C`
after isolated ambient grid vertices are discarded, and

```text
beta(C) = |E(C)|-|S|+c_S
```

is its cycle rank.  OCB denotes the candidate

```text
W(C) >= n+1+c_S.                                      (OCB)
```

## Exact line ledgers

For primal row `r`, let:

- `s_r` be the number of supported vertices;
- `h_r` be the number of horizontal cotree edges;
- `x_{r-1},x_r` be the numbers of vertical cotree edges crossing the strips
  immediately above and below the row;
- `p_r=s_r-h_r` be the number of components of the horizontal cotree graph in
  that row, counting isolated vertical endpoints;
- `k_r` be the number of runs of supported vertices in the row; and
- `g_r=p_r-k_r` be the number of missing horizontal cotree edges whose two
  endpoints are nevertheless supported.

The following are exact identities, checked independently in rows and columns:

```text
w_r = 3s_r-2h_r-x_{r-1}-x_r
    = s_r+2p_r-x_{r-1}-x_r
    = s_r+L_r+R_r+2g_r-x_{r-1}-x_r,                 (1)

W(C) = sum_r w_r.                                    (2)
```

Here `L_r=R_r=k_r` count left and right support-run endpoints.  Pointwise,
`w_r` is also exactly `sum_{v in S_r}(3-deg_C(v))`.  Thus (1) is the requested
decomposition into left/right endpoints, vertical cotree crossings, and degree
deficits.  `turns_r` is also reported by the script, but no valid coefficient
for turns was needed for either exact identity.

The graph ledger gives a second exact form:

```text
W(C) = |S|+2c_S-2 beta(C).                            (3)
```

Every grid-tree cotree support covers every row or every column.  In a covering
orientation, `|S|-n=sum_r(s_r-1)`, so OCB is exactly equivalent to

```text
2 beta(C)+1 <= sum_r(s_r-1)+c_S.                     (4)
```

Equation (4) is the robust invariant exposed by the census: support excess and
component credit must pay two units per independent cotree cycle and one final
unit.  It is not proved here.  A local strip proof of OCB can target (4), while
(1) supplies the exact conversion back to incidence waste.

## Failed local allocations

Assigning each cotree component to its first supported row gives a root count
`b_r`.  The tempting line inequality

```text
w_r >= 1+b_r
```

is false already on `2x2` and `3x3` trees.  Its prefix-sum version is also
false; among all `4x4` trees the minimum prefix of
`sum_r(w_r-b_r-1)` is `-2`.  Empty rows in one orientation are not the whole
issue: OCB-tight `4x4` examples can have an uncovered row while all columns are
covered.  Any proof must choose the covered orientation and permit charge to
cross strips.  Root charges confined to their birth row cannot work.

Turns are useful diagnostics for these transfers but do not themselves alter
the exact debt: cycles contribute the `2 beta(C)` term in (4).  A next local
candidate should allocate each cycle-rank birth to two support-excess tokens in
the strip frontier, retaining one component/final token globally.

## Census

`analysis/bounds/cotree_row_charge.py` produced:

| family | trees | minimum OCB slack |
|---|---:|---:|
| all `2x2` spanning trees | 4 | 0 |
| all `3x3` spanning trees | 192 | 2 |
| all `4x4` spanning trees | 100,352 | 0 |
| Wilson samples, each `n=5..12` | 500 per size | nonnegative |
| maximum-F witnesses, `n=3..9` | up to 100 per size | nonnegative |

The minimum sampled Wilson slacks for `n=5..12` were
`9,18,28,38,49,69,84,104`.  The maximum-witness minima for `n=3..9` were
`2,0,3,2,0,3,2`; enumeration was complete where the witness family had at most
100 members (`n=3,4,6`) and capped otherwise.  Each forced witness was extended
to an actual spanning tree before measurement.

One OCB-tight `4x4` cotree has

```text
(W,|S|,c_S,beta) = (6,8,1,2).
```

In its covered column orientation the support counts are `(1,3,3,1)`, so the
right side of (4) is `(8-4)+1=5`, exactly `2*2+1`.  This shows that both the two
units per cycle and the final unit in (4) are sharp in the smallest nontrivial
tight census.

Run:

```bash
PYTHONPATH=analysis python3 -m analysis.bounds.cotree_row_charge
PYTHONPATH=analysis python3 -m unittest analysis/tests/bounds/test_cotree_row_charge.py
```
