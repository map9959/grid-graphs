# A deficit ledger for nonperiodic cuts

For a one-gap equality candidate put `k=39+14t`, `n=3k+2`, and
`D=198+72t`. No cut, band, sequence of masks, or sequence of
component partitions is assumed to repeat in the horizontal direction.
There is now both a charge for **new root obligations** and a lower
bound on the **total cross-cut traffic** needed at this budget.

### What is carried

Sweep whole tile columns from west to east. Work in the crop, with
one root attachment per tooth. Equivalently join marks at distance one
and join axially separated marks at distance two if the intervening
site is unmarked. There are no diagonally adjacent marks (a forced
square cycle); suppressing the intermediate vertex of a hop and
removing unmarked leaves preserves the marked components. Since a
tile column is three sites wide, a hop crosses at most one cut.

Let `J_i` be the number of hops from column `i` to `i+1`. Missing
exterior cuts have zero traffic. In the restriction to column `i`
alone let `R_i` be the number of marked components without a tooth,
and `b_i` the number of those without an incident hop from the west.
These latter components each receive a new birth label. Let `U_i`
be the number of still-unrooted marked components in the **whole
processed prefix**. Then, exactly,

```
ΔU_i = U_i - U_{i-1} = R_i - J_{i-1},     U_{-1}=U_{k-1}=0.
```

Indeed before inserting the crossing edges the two pieces have
`U_{i-1}+R_i` independent unrooted trees. Every edge must join distinct
components and at most one can already have a tooth. Each such join
reduces the count by one. This is an identity for actual rooted
partitions, not a sufficient numerical test for gluing.

When two unrooted trees merge, **both sets of birth labels continue
on the merged tree**. A label is paid only on reaching the unique
physical tooth. Thus every unrooted class has at least one active label;
several can be paid together. Births are counted when their whole
column has been added, so transient partial-column components do not
earn labels.

### A lower deficit inequality that pays at the tooth

Let `d_i` be the deficit of column `i` and let `w_i=d_{i-1}+d_i+d_{i+1}`,
repeating the endpoint column in place of a missing neighbor. Hence
`sum w_i = 3D`. Two finite-state price tests give, for `p=2,6`,

```
w_i + ΔU_i >= f_p(i) + p*b_i.
```

The two seven-column fringes use the tables in `component_debt_audit.F`
(entries 0–6 and 8–14); entry 7 is the generic bulk value. In the
intervening bulk, `7<=i<=k-8`, the price pairs `(f_2,f_6)` are:

| Condition (first applicable) | Axis 1 | Axis 2 |
|---|---:|---:|
| At least one column in the centered triple has both long arms | (16,12) | (16,12) |
| Triple beyond the north isolate halo to its east | (9,5) | (9,5) |
| Otherwise | (6,2) | (5,-19) |

Here “long” means north `6,7^12` and south `448^11,192`, in transposed
masks. For an east-of-isolate triple the north rim is in the
post-star phase throughout the triple. For instance if `d=2+3q`, it
suffices that `i-1>=q+3`. In either of the first two cases we also
verified `w_i - ΔU_i >= f_2(i) + 2*b_i`.

Set `s_i=f_2(i)-f_6(i)`. Let `z_i` be the maximum of zero,
`4*b_i-s_i`, and (only in the first two bulk cases) `2*ΔU_i`.
The combined bound is `w_i + ΔU_i >= f_2(i)+2*b_i+z_i`. Assign the
`2*b_i+z_i` credits among this column's new labels. This is possible
even when there are none: `ΔU_i<=b_i` and `s_i>=0` imply `z_i=0`
in that case. Let `P_i` be the total value of labels still carried
after the cut, **minus** `U_i`. If `g_i` is the value actually grounded
at a tooth in step `i`, we obtain the nonperiodic inequality

```
w_i >= f_2(i) + g_i + P_i - P_{i-1}.
```

No continuity of marks between guessed donors is used. In particular,
this inequality does not pay a merged component off before it finds
its root. On any subinterval the endpoint potentials remain in the bill;
on the full square both are zero.

Writing `B=sum b_i`, `Z=sum z_i`, `L` for the number of bulk triples
meeting a long column and `E` for those beyond the isolate not already
counted in `L`, summing at the equality budget gives:

```
axis 1:  2B + Z + 3E + 10L <= 340+132t
axis 2:  2B + Z + 4E + 11L <= 371+146t
```

The generic base sums are `6k+20` and `5k+28` respectively. Thus the
price of creating many new trees is quantitative, even if their final
connections occur at quite different columns.

### Complementary bound: traffic the cuts must carry

Put `X_i=max(0,J_i-1)`. A signed-cost transfer in the other direction
gives

```
d_i <= a_i + ΔU_i + c_i*(X_{i-1}+X_i).
```

Here `a_i=4`, except that the last column uses 6 and each bulk triple
beyond the isolate uses 3. Set `c_i` to 4 at the two endpoints, 2 in
their immediate neighbors and 3 elsewhere. Let `E_all` count all the
bulk triples beyond the isolate. Cancellation now requires

```
6 sum X_i >= 40+16t + E_all + X_1 + X_{k-3}.
```

For example at 623 (`t=12`) at least **39 excess hops** are required;
for the distance-five isolate the bound is **71**. These are hops
beyond the first on their respective cuts, not necessarily distinct
overloaded cuts. This rules out a single-port chain without assuming it
is periodic; disregarding the positions and destinations of all extra
hops would not be a valid construction.

There is a further lifetime test on sparse stretches east of the
isolate. If both incident cuts of a bulk column have at most one hop,
they each have exactly one, and the column deficit is exactly three.
Contract the prefix to its true rooted or unresolved port. A rooted
incoming port can only stay rooted. For an unresolved incoming port
there are just two possibilities: the *same* component travels on,
or it reaches a tooth and a *different* one is born. Let `y` be the
longitudinal physical coordinate of the unique hop. It cannot decrease
on a carry, and it increases by at least four on a payment-and-rebirth.
The DP prices `y_right-y_left` by adding the cumulative left-minus-right
hop count at every physical site. Over a nonperiodic stretch of `m`
such columns with `g` payments-and-rebirths,
`sum d_i + y_last-y_first >= 3m+4g`. The penultimate column cannot
have at most one hop on both sides even without a deficit constraint.

### Evidence and limits

The bounded-width computation uses the existing certified physical
catalogues, taking a union over applicable star phases. All plaquettes
and forced-edge partitions within a triple share physical variables.
The inner partition independently records mark presence, tooth, and
actual left/right **mark hops** per tree, not just proximity to a cut.
Finishing a marked class without a tooth or an exit is forbidden.
For the signed prices the checker takes a coordinatewise minimum over
14-step additions until it verifies `T^14(v)>=v` at **every** state,
then attaches the far fringe. A failed stationarity test would not
certify a price. The port test instead closes over all extra lengths.

The all-size sum alone does **not** exclude the budget. The audit gives
an explicit scalar control at `d_i=5` or `6`: pairs of new lineages
merge before a later tooth pays the accumulated labels, and the total
is `198+72t`. Only the inequalities and ledger are being tested by this
control. It is not a mark assignment. Independently, graph traversal on
two previously rooted regions pays 31 and 61 birth labels respectively
and checks each final physical tooth. A branching graph regression
checks that both labels survive an intervening merge. No spanning tree
is claimed and no new SAT proof files are needed.

The payment identity, subinterval telescoping and final arithmetic are
checked in [`CutDebt.lean`](../lean/GridGraphs/Geometry/CutDebt.lean);
the local prices and port transitions are checked by the Python replays.
The [ordered two-port transfer](ORDERED_TWO_PORTS.md) shows the excess
cannot be distributed entirely among cuts with exactly two hops.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.component_debt_audit
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.debt_ports
```
