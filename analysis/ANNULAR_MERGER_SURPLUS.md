# Annular merger surplus

This note continues the exact outer-layer ledger in
`BOUNDARY_PEELING_LEMMAS.md`.  It does not modify or assume more than the
forced-forest hypothesis there.  The main outcomes are an exact radial
reduction of the merger conjecture, complete verification at `n=5`, and two
counterexamples ruling out natural scalar inherited-surplus inductions.  A
noncircular proof of `W>=n+2` is not obtained.

## 1. Radial types and an exact reduction

Orient every radial edge from its boundary endpoint to its inner endpoint and
write

```text
r_UU, r_UF, r_FU, r_FF
```

for the four endpoint types.  Thus

```text
rho_U = r_UU+r_FU.
```

Let `a_H` and `a_F` be the numbers of attached boundary backbones in the two
component-incidence forests.  The radial teeth are exactly

```text
t_H = r_UF+r_FU+r_FF,
t_F = r_FF.
```

Every nontrivial component-incidence graph is a tree, so its merger rank is
teeth minus attached boundary vertices.  Consequently

```text
mu_H = t_H-a_H,
mu_F = t_F-a_F.                                      (1)
```

This proves the following exact equivalence, with no inequality used:

```text
rho_U-mu_F-mu_H
  = a_H+a_F+r_UU-r_UF-2r_FF.                         (2)
```

In particular, the conjecture `mu_F+mu_H<=rho_U` is precisely the radial
backbone inequality

```text
a_H+a_F+r_UU >= r_UF+2r_FF.                          (R0)
```

The cancellation of `r_FU` is useful.  It also shows exactly what a proof must
use: the labels on the first two layers, the attached boundary runs, and the
fact that their component-incidence graphs arise from one planar grid forest.
Arbitrary abstract incidence forests do not satisfy `(R0)`.

The finite evidence supports the stronger statement

```text
a_H+a_F+r_UU >= r_UF+2r_FF+4,       n>=4.            (R4)
```

Equivalently, `mu_F+mu_H<=rho_U-4`.  Equality occurs at `n=4,5,6`, so the
constant four cannot be increased.  No proof of `(R0)` or `(R4)` is claimed
here.  The smallest remaining merger lemma is `(R4)`: it has no component
counts or inherited ledger terms left, but forest-valid planar realizability
is essential.

## 2. Exact and randomized evidence

`check_annular_merger_surplus.py` independently constructs both incidence
forests and checks `(1)` and `(2)`.  Complete enumeration through `n=4` gives

```text
n    forest-valid patterns    min(rho_U-mu_F-mu_H)
3             100                         0
4           2,278                         4
```

`check_annular_merger_surplus_n5.cpp` examines all `2^25` patterns, rather
than sampling or pruning them.  Its result is

```text
forest-valid patterns                    116,252
minimum rho_U-mu_F-mu_H                        4
minimum L_5                                   12
```

One equality witness for the merger margin is

```text
UUUUU
.....
UUUUU
UUUU.
U..U.
```

It has `(mu_F,mu_H)=(0,3)`, `rho_U=7`, and radial data

```text
(a_F,a_H;r_UU,r_UF,r_FU,r_FF)=(2,5;4,3,3,2).
```

A seeded sample of 200,000 patterns at `n=6` retained 37,476 forest-valid
patterns and had minimum margin six.  A separate deterministic local search
found margin four, with witness

```text
UUUUUU
......
UUUUUU
U.UUU.
U.UUU.
U.U.UU
```

Thus there is no counterexample to `(R0)` through exhaustive `n=5` or the
reported `n=6` searches.  Only the exhaustive claims are proofs over their
stated finite domains.

## 3. Why inherited surplus has not closed the induction

Put

```text
P_n = L_n-(n+4).
```

For one annulus the exact ledger gives

```text
P_n-P_(n-2)
  = Q_U-Q_U^o+s_F+s_H-mu_F-mu_H-2.                  (3)
```

Requiring the inherited surplus to cover the negative part of the right side
of `(3)` is exactly `P_n>=0` after substitution.  It is therefore a
restatement, not a strengthened induction.

### Two-annulus scalar pooling fails

The natural noncircular candidate

```text
L_n >= L_(n-4)+4                                    (4)
```

would imply the target by induction in steps of four.  It is false at `n=6`.
The smallest found counterexample is

```text
....U.
UUUUU.
U.UUU.
U.UUU.
UUU.U.
..UUU.
```

Its forced graph `H` is a forest, while

```text
L_6=15,       L_2(center)=12,       L_6-L_2=3.
```

Complete enumeration gives a minimum increment of eight from the empty
`0 x 0` center at `n=4`; regular two-annulus peeling through `n=5` has a
degenerate `1 x 1` center.  Thus `n=6` is the first regular size at which `(4)`
can fail.  The checker preserves and verifies the mask `30458370000`.

### A linear boundary potential is impossible

Another genuine attempt is to make

```text
S_n=P_n-alpha Q_U
```

nondecreasing under every annular extension.  By `(3)`, this requires

```text
(1-alpha)(Q_U-Q_U^o)+s_F+s_H-mu_F-mu_H >= 2.         (5)
```

Two forest-valid `4 x 4` patterns make the feasible interval empty.  The mask
`3942` displayed in the preceding boundary-peeling note has

```text
Q_U-Q_U^o=-4,       s_F+s_H-mu_F-mu_H=0,
```

so `(5)` forces `alpha>=3/2`.  The pattern

```text
.U.U
UU.U
UUUU
....
```

has mask `4026` and data

```text
Q_U-Q_U^o=1,        s_F+s_H-mu_F-mu_H=1,
```

so `(5)` forces `alpha<=0`.  Hence no potential consisting of surplus plus a
fixed multiple of boundary deficiency can supply the induction.

These failures are structural: scalar surplus forgets which inner components
own the radial ports.  Any viable inherited potential must retain at least a
component-resolved radial state (and probably its four-side order), not merely
`P`, `Q`, or a fixed number of pooled annuli.

## 4. Rigorous status and remaining lemma

The following are proved here:

1. the exact identity `(2)` reducing the merger conjecture to radial types and
   attached backbones;
2. `(R4)`, hence the original merger conjecture, for every pattern through
   `n=5` by complete enumeration;
3. failure of the two-annulus scalar inequality `(4)` at the first regular
   possible size `n=6`; and
4. impossibility of every monotone linear potential `P-alpha Q`.

The smallest unresolved structural statement is `(R4)`.  Proving it would give
a strict merger reserve, but it still would not by itself prove `W>=n+2`, since
`Q_U^o` is subtracted in `(3)`.  The remaining induction problem is therefore
sharply separated into two tasks: prove `(R4)` by planar radial separation, and
identify a component-resolved inherited potential whose transition inequality
is stronger than the tautology `P_n>=0`.  No scalar candidate tested here meets
that second requirement.

## 5. Reproduction

Run the unit checks and randomized search with

```text
python3 -m unittest analysis/bounds/check_annular_merger_surplus.py
python3 -m analysis.bounds.check_annular_merger_surplus --random-n 6 --trials 200000
```

Run the complete `n=5` census with

```text
g++ -O3 -march=native -fopenmp \
  analysis/check_annular_merger_surplus_n5.cpp \
  -o /tmp/check_annular_merger_surplus_n5
/tmp/check_annular_merger_surplus_n5
```
