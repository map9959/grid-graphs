# Affine Residue-Two Pump

`residue_two_affine_pattern(n)` is the best current parametric candidate for
`n=3k+2`, `k>=5`. Every checked member is dual-connected and
forest-completable, but the family still lacks an inductive connectivity proof
and has a linear surplus over the conjectured minimum.

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

`check_affine_residue2.py` reconstructs the pump implementation from the finite
base-word source codes

```text
rows:    (0..8) (9,10,11)^(k-4) (12..16)
columns: (0..3) (4,5,6)^(k-4) (7..16),
```

and checks the displayed U-count, induced-edge count, and cycle-excess formulas.
Its optional topology checks remain finite computation rather than induction.

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
three-for-three exchange. It was the first concrete target for the missing
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

## Full-Middle Grammar

`search_residue_two_middle.py` tests a larger constant-surplus control language
at `n=20`. It fixes affine rows 0--2 and 18--19 plus the two boundary columns,
then represents each of the 90 interior three-cell packets by one of

```text
L=UU.  X=U.U  R=.UU  H=UUU.
```

The five fixed rows cost 54 U, every packet costs two U, and an exact quota of
16 H packets gives `54 + 180 + 16 = 250` U. This is the constant-surplus-one
target; the conjectured exact target at `n=20` is 249 U. Exact frontier
partitions are retained inside a topology- and quota-diverse beam. The search
now expands from both fixed caps, streams each row packet-by-packet, and joins
the exact retained frontier partitions. A beam of 100 found a valid 250-U state
with connected dual cycle excess two. Its count differs from the 179-U `n=17`
base by 71, exactly `q(20)-q(17)`, so the two states have the same surplus one;
an explicit recurrence mapping between them is not yet known.
No single deletion is valid, and every global one-addition/two-removal trim is
negative. At 249 U, beam 100 reached a two-component join but no witness.

The grammar is generalized to larger `n`. At `n=23`, beam 20 reached six
components for the 333-U constant-surplus target and eight for the exact 332-U
target. All failed beams remain non-exhaustive.

The `phase` alphabet adds the residue-zero center seam `S=.U.`; `balanced` adds
all one-U packet orientations. Charge is measured relative to two U per packet,
so `H` has charge +1 and a seam has charge -1. This permits topology-changing
H/seam pairs at fixed total count, but the first bounded seam beams have not yet
found a quota-compatible connected join.

A narrower moving-phase grammar subsequently found another valid 250-U state.
Every row has form `. L^a C R^(k-a-|C|) .` with `C` over `X/H` and
`|C|<=5`. Unlike the first 250-U state, its connected dual is unicyclic. It has
no valid single deletion, no one-packet H downgrade, and no global
one-addition/two-removal trim. A beam-500 exact-count run in the same row
language still reaches only a two-component join.

Exact searches around the retained 249-U rectangle defect now rule out local
cell exchanges through order four, all binary packet changes through radius
four in the specified halo, and several suffix/two-lobe phase corridors with
alternate caps. See `RESIDUE_SHARED.md` and the corresponding JSON result
artifacts for exact scopes. The five-column two-lobe DP initially exceeded the
one-direction time bound, but an in-memory bidirectional solver completed it.
At cut `9/10`, none of 6,090 lane-counted compatible state pairs
is connected, giving an exact negative for that declared five-column language.

For `n=23`, the failure of the fixed affine cap is now isolated: affine top
depth three admits no legal bounded phase row, while depth four admits 212 and
the reflected bottom sandwich admits 63. An exact affine/D4 cap census records
841 one-step-live, charge-feasible full-state pairs for each of targets 332 and
333. No middle search has yet connected those cap seeds.

## Run/Rank Relaxation

`certify_residue_two_relaxation.py` records a hierarchy of genuine necessary
conditions for the exact 178-U target at `n=17`. Dual connectivity requires at
least 256 U-U edges. If `R_row` and `R_column` count maximal U-runs, then

```text
E = 2|U| - R_row - R_column,
```

so every target must have `R_row + R_column <= 100`. The old bundled witness
passes that scalar bound and coarse block ranks, but face `(12,3)` has singleton
cut zero. The strengthened hierarchy adds all singleton and row/column interval
cuts, bounded rectangles, seam-preserving quotients, and radius-one
contracted-exterior windows.

An exhaustive one-for-one search from all three near-hits checks 59,274
candidates; four pass rectangles and none pass the seam quotients. A bounded
100,000-candidate second hop also finds no seam-quotient-feasible state. These
are restricted-neighborhood results, not an impossibility proof.
