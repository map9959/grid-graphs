# Reducing the linear boundary term to straight cap intervals

For every residue-one square at or above the comb, on **each** side
one can cut off a cap of depth `d=o(sqrt(n))` with the following two
properties simultaneously:

* `d` tends to infinity, and the inner cut is a pitch-or-full path in
  three adjacent rows (columns on a vertical side);
* if it has `K` straight pieces, **`dK=O(n/log n)`**.

This product matters: splitting the cap transversely at every piece
costs only `o(n)` boundary sites in total. A bound just on the number
of pieces in a deep cut would not suffice at the linear scale.

Use disjoint dyadic bins of block indices `[2^j,2^(j+1))` between
`n^(1/8)` and `n^(1/4)` measured inward from the chosen side. There
are `Θ(log n)` bins. The total bill is `O(n)` by the run/component
ledger, also after reflecting the board. Some bin of length `D`
has total bill `O(n/log n)`. A block in it therefore has
`D e = O(n/log n)`, at depth `d=O(D)`. The
[detour construction](RESIDUE_ONE_CHEAP_SEPARATORS.md) gives
`K=O(1+e)` as claimed. Choose the four cuts independently on the
original marking. Discarding corner boxes where their arms meet costs
`O(n^(1/2))=o(n)` sites. Trimming a partially cut piece there adds
only a bounded number of new ends.

In particular the untied outer caps on these four sides can be
split into rectangles, with total artificial transverse boundary
length `O(n/log n)`. Extra or missing terminal *classes* caused by
such splitting are also at most of this order: deleting one crossing
edge increases the number of components by at most one. Keep the
whole longitudinal mark profile in each remaining rectangle. This
statement permits an asymptotic cap inequality with an error
proportional to its height **per piece**; it does not permit assuming
that maximum depth nine is sufficient.

There is a simple universal price for **full** pieces: in a free
`L × (d+1)` rectangle whose inner row is entirely marked, the other
`d` rows contain at most `dL/3 + 2(d+1)/3` marks. Indeed the forest
ledger is `3M=area+marked boundary incidences-R-c`. The two long
ends have at most `2L` incidences, the two short ends at most
`2(d+1)`. Subtract the `L` fixed marks. For `d` divisible by three,
straight bars at spacings of three attain the leading term. For a
pitch piece this argument loses a linear term; the rank of the
partition of its teeth must be priced.

For full pieces, the [neighbor-square exchange](FULL_BAR_EXCHANGE.md)
improves the bound by `31L/210` at depth `1 mod 3` and by `L/10` at
depth `2 mod 3`, up to the permitted `O(d)` end error.
