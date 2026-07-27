# Affine Residue-Two Pump

`residue_two_affine_pattern(n)` is the best current parametric construction for
`n=3k+2`, `k>=5`. It is dual-connected and forest-completable, but it has a
linear surplus over the conjectured minimum.

## Base

The base is the connected 179-U pattern at `n=17`. It is obtained from the
cached exact `n=14` witness by changing old cell `(4,8)` from U to a dot,
inserting three rows before row 6, inserting three columns before column 7 or
8, and placing 61 U vertices in the inserted cross. Thus

```text
179 = 119 - 1 + 61 = q(17) + 1.
```

Its dual has 257 vertices and 257 edges, is connected and unicyclic, and the
forced forest completes to a spanning tree.

## Pump

Given a pattern of width `m=3k+2`, form width `m+3` by duplicating rows 9, 10,
11 immediately before row 9 and columns 4, 5, 6 immediately before column 4.
Equivalently, use index lists

```text
rows:    0..8, 9,10,11, 9..m-1
columns: 0..3, 4,5,6, 4..m-1.
```

This is a fixed two-marker control state after the exceptional `14->17` start.

## Counts

For `n=3k+2`, `k>=5`, the construction has

```text
|U_k| = 6k^2 + 6k - 1
      = q(3k+2) + k - 4.
```

The pump increment is

```text
|U_(k+1)| - |U_k| = 12k + 12,
q_(k+1) - q_k       = 12k + 11.
```

Therefore each pump increases the surplus by one. The resulting spanning tree
has at least `3k^2+6k+5` full-degree vertices, `k-4` below the conjectured
residue-two value.

## Dual Edges

The induced U-U dual has

```text
E_k = 9k^2 + 8k - 8,
V_k = 1 + (3k+1)^2 = 9k^2 + 6k + 2.
```

When connected, its cycle excess is `E_k-V_k+1=2k-9`.

The checker confirms dual connectivity and forced-forest completion for every
generated member through `n=119`. This is computational verification, not yet
an inductive proof of dual connectivity.

## Exact-Count Status

The conjectured n=17 target is 178 U vertices. Several 178-U patterns reach one
isolated dual face, but no valid target witness is known. The connected 179-U
base has no valid trim within any of these complete neighborhoods:

```text
one addition / two removals,
two additions / three removals,
three additions / four removals,
four additions / five removals.
```

The exact affine 178-U packet is also negative under unrestricted global
two-for-two and three-for-three exchange. These are neighborhood certificates,
not a proof that 178 U is globally impossible.

The next constructive goal is a second pump control state whose transition
saves one U relative to the affine pump while changing the frontier attachment
state. A one-off trim at n=17 would not by itself remove the growing surplus.

At n=20, the affine member has 251 U. Complete global checks rule out every
single deletion, one-addition/two-removal trim, and two-addition/three-removal
trim to 250 U. A separate 250-U affine-lift candidate reaches `361/362` dual
faces but is globally negative under bridge-containing two-for-two and
three-for-three exchange. This is the first concrete target for the missing
second control state.

The stable `17->20` pump inserts rows 9--11 and columns 4--6 with cross cost 72.
An exact binary-cell search proves that the frozen-exterior cross cannot cost
71: after contraction, connectivity needs rank 118 while every cost-71 cross
has rank at most 116. Allowing the complete mutable column slab 0--6 is also
exactly negative at 250 U after 40,595,328 transitions.

The closest cycle-saving B state reconverges with the affine frontier after row
16 in mask, partition, and cost, but has one less accumulated cycle. Exhausting
all 77,520 cost-neutral 13-U row-16 masks leaves only 15 topology-valid incoming
states; 32,360,464 exact suffix joins prove that none has a connected three-row
suffix of cost 32. Finally, the connected 251-U affine member has no global
three-addition/four-removal trim to 250 U. The second state must therefore alter
an earlier prelude and the closing cap together; it cannot be represented by a
cross-only saving, a seven-column slab, or a late three-row suffix.

That split control was tested next. With affine rows 4--15 frozen, an exact
top-four/bottom-four synthesis checks 148,906,752 transitions and has no
connected 250-U join. A topology-guided three-box decomposition then couples
the early cycle, delayed reroute, and OUT cap. All 188 add/remove quota
distributions and 6,121,741 MITM signature pairs are negative. The sharp
one-face state produced by that language has no global repair through
three-for-three exchange. A successful B state must therefore change part of
the affine middle itself, not just its cross, prelude, suffix, or three
currently identified control boxes.
