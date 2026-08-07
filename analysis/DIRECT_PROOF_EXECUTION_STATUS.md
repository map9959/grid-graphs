# Direct proof execution status

This note records the result of executing the direct proof program proposed for
the diagonal grid problem.  Several foundational lemmas are now proved and
checked, but the program does not yet prove the arbitrary-width lower bound or
the revised residue-two construction.  The distinction matters: the remaining
statements are global extremal and construction theorems, not missing algebra.

## 1. Universal-bound formulations

For a dual spanning tree `D`, let `U=supp(D)` and let `T` be the complementary
primal spanning tree.  The following targets are equivalent:

```text
W(D)>=n+2,
2N_1+N_2>=n+2,
Q+S>=n+2,
3|F|<=n^2+3n-4,
Q_U+c_F+c_H>=n+4.
```

In the fourth line, `F` is the set of vertices having full grid degree in `T`.
In the fifth, `H=G-E(G[U])` is the forced forest.  The full-degree formulation
shows that the missing result is a theorem about arbitrary spanning trees of
the square grid; it does not depend on choosing a special dual basis.

`FULL_DEGREE_GRID_TREE_BOUND.md` proves these equivalences and exhaustively
checks all spanning trees through `n=4`.  The minimum wastes are `4,7,6` at
`n=2,3,4`; equality `W=n+2` first occurs at `n=4`.

## 2. Proved direct lemmas

The following steps of the program are complete.

1. `BOUNDARY_PEELING_LEMMAS.md` proves comb separation, exact outer-layer
   deletion, and the exact annular merger ledger.
2. `LAMINAR_MULTI_EXCHANGE.md` proves the arbitrary exchange formula

   ```text
   Delta W=3(|new support|-|lost support|),
   ```

   rooted fundamental-shore laminarity, the contracted-tree compatibility
   criterion, bond-cycle duality, and sharp protector inequalities.
3. `FOREST_EXTREMAL_INDUCTION.md` proves the exact `U -> F` exchange criterion
   and the maximal-counterexample repeated-label normal form.
4. `ANNULAR_MERGER_SURPLUS.md` reduces the proposed merger reserve to the exact
   radial identity

   ```text
   rho_U-mu_F-mu_H=a_H+a_F+r_UU-r_UF-2r_FF.
   ```

5. `INCIDENCE_WASTE_EQUALITY.md` proves the algebraic equality and near-equality
   reductions and checks all available equality controls.

These lemmas narrow the universal problem but do not sum to its conclusion.

## 3. Failed globalization routes

Exact counterexamples now rule out the following proposed shortcuts.

1. A full side need not survive in the complementary primal tree.
2. Owner-only Hall charging fails from `n=17` onward, even after greedy
   maximalization.
3. A single unsupported protector may serve several nested fundamental cuts.
4. Separately valid fundamental-cut choices need not form a simultaneous tree
   exchange.
5. The annular increment `L_n-L_(n-2)` can be negative; it equals `-4` on a
   forest-valid `4 x 4` pattern.
6. The two-annulus inequality `L_n>=L_(n-4)+4` fails at `n=6`.
7. No scalar potential `P-alpha*Q` is monotone under every annular extension.
8. The radial reserve cannot be proved from the labelled annulus alone: an
   annular forest has reserve three, although it has no full-grid completion in
   the checked widths `5<=n<=8`.
9. Maximal repeated labels have unbounded component reuse and are logically
   equivalent, rather than strictly weaker, than the original theorem.
10. Fixed or moving scalar three-row production is false on known equality
    controls.

Thus any valid proof must retain component-resolved interior attachment data.

## 4. Exact remaining universal lemma

Two coupled facts are still required.

> **Boundary-rooted two-forest rank.** When an outer grid cycle is attached to
> an inner forced forest, the sum of the ranks with which it merges components
> of `H` and `G[F]` is at most the weighted inner-boundary `U` count minus four.

This is the radial inequality `R4` in `RADIAL_BACKBONE_INEQUALITY.md`.  It is
verified exhaustively through `n=5`, but unproved.  Even after `R4`, one needs:

> **Component-resolved telescoping.** There is an inherited attachment state
> whose annular transition charge is nonnegative and whose initial and terminal
> values differ by `n+2`.

A scalar surplus is insufficient.  The state must remember which inner
components own radial ports and their cyclic order.  Proving these two facts
would yield `W>=n+2`.

## 5. Equality and residue-two tail

Assuming the universal bound, equality classification still requires a
width-independent attachment phase theorem.  The exact consequences would be:

```text
W=n+2 only when n=1 (mod 3),
K>=4,2,5 for n=0,1,2 (mod 3).
```

For `n=3k+2`, a `K=5` candidate has exactly `W=n+5` on full dual-tree support.
The committed `n=17` search excludes that case at the first tail width.  The
bounded reverse analysis in `N17_HISTORY_RECOVERY.md` proves positive terminal
debt earlier for 18 of the 20 survivors, but two states merge zero- and
positive-deficit histories.  Their predecessor choice was discarded by the
original minimum-cost state projection.

The missing tail theorem remains a width-independent silent-hull coverage and
persistent-debt result.  Current artifacts prove it at `n=17`, not for every
`k>=5`.

## 6. Revised construction

For `n=3k+2`, the revised target is

```text
T(k)=6k^2+5k+4,
T(k+1)-T(k)=12k+11.
```

The packet count recurrence is exact, but it does not preserve rooted dual
attachment.  The first uniform-right candidate at `n=23` has 333 U vertices,
eight dual components, and cycle excess six.

The complete straight-cut open-slab census found no target-cost interface:

```text
A17 -> B20:          3,322 exact-charge cuts, 0 exact interfaces,
B20 -> affine A23:   3,516 exact-charge cuts, 0 exact interfaces.
```

Every closest cut forgets exactly one slab-only component.  Retaining one extra
dual port closes that finite interface at zero U cost, but no target-count
pattern carrying the wider interface is known.

Further exact neighborhood searches found no 333-U construction:

```text
55,945       two-U deletions from affine A23,
4,856,390    bounded seam exchanges around affine A23,
44,953,544   one- and two-swap repairs of the symbolic 333-U candidate.
```

The affine pump remains the strongest proved construction recurrence.  It adds
`12k+12` U vertices, one more than the revised target, and is directly verified
through `k=40`.  A complete exact formula therefore still needs a new rooted
open-slab transfer or a different construction family.

## 7. Current conclusion

The execution produced rigorous new lemmas and finite negative certificates,
but not the requested arbitrary-width conclusion.  The three irreducible open
obligations are now:

1. prove the boundary-rooted two-forest rank plus a component-resolved
   telescoping potential;
2. classify zero-defect and defect-three attachment phases in arbitrary width;
3. construct an exact-charge rooted open-slab transfer with no hidden live
   component.

Claiming the exact diagonal theorem before these statements are proved would be
circular or would contradict one of the explicit counterexamples above.
