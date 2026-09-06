# Boundary-charge reduction census

This is finite computational evidence, not a proof for uncomputed widths.

## Definitions and identities

Let `F` be forced, `U=V\F`, and let `H` contain exactly the grid edges with at
least one endpoint in `F`. Define

* `B_F = sum_{v in F} (4-deg_G(v))`;
* `d_F(u) = |N_G(u) intersect F|` for `u in U`;
* `U0 = |{u in U : d_F(u)=0}|`, the isolated `U` vertices of `H`;
* `R = sum_{u in U, d_F(u)>=2} (d_F(u)-1)`, the branching credit;
* `C` as the number of components of `H` other than those `U0` vertices.

For acyclic `H`, direct edge counting and the component-incidence quotient give

```text
c(G[F]) = C + R,
|E(H)| = n^2-U0-C,
|E(H)| = 4|F|-B_F-(|F|-c(G[F])).
```

Therefore the exact identity is

```text
3|F| = n^2 + B_F - U0 - R - 2C.
```

Thus `B_F-U0-R-2C <= 3n-4` is exactly equivalent to
`3|F| <= n^2+3n-4`; it is not a lossy sufficient reduction.

## Coverage and results

`boundary_charge_reduction.py` independently reconstructs all quantities from
row masks and asserts both identities. It checked every forced-acyclic set at
`n=3,4`: respectively 100 and 2,278 sets, with no identity or target failure.
There are 14 equality sets at `n=4`, exactly the 14 maximum sets.

The existing exact maximum-witness generator was exhausted through `n=6`:

| n | maximum witnesses | `|F|` | `B_F-U0-R-2C` | target `3n-4` | equal |
|---:|---:|---:|---:|---:|---:|
| 3 | 24 | 4 | 3 | 5 | 0 |
| 4 | 14 | 8 | 8 | 8 | 14 |
| 5 | 242 | 11 | 8 | 11 | 0 |
| 6 | 96 | 16 | 12 | 14 | 0 |

Cached/canonical certified maximum witnesses were checked at every width
`n=7..12,14,15`, plus four distinct witnesses at `n=9`. Their charge values
were respectively `17,17,21,26,26,30,35,39`; no target violation occurred.
Equality occurs at certified widths `n=7,10`. The target-count `n=13` witness
also has equality (`|F|=68`, charge 35), but `data/diagonal.csv` currently marks
that width only as a lower bound, so this census does not call it maximum.

## Strongest simple coefficients

The script tested every integer triple `(a,b,c)` in
`{0,1} x {0,1} x {0,1,2}` for

```text
B_F - a U0 - b R - c C <= 3n-4.
```

The unique Pareto-strongest surviving triple is `(1,1,2)`, the exact identity
triple. Each attempted reduction has an explicit counterexample:

* Omitting `U0`, `(0,1,2)`, first fails in the exact augmented row grammar at
  `n=7`. The witness below has `|F|=19`, `B_F=23`, `U0=10`, `R=3`, `C=1`.
  Its stronger left side is 18, exceeding 17; the identity left side is 8.
* Reducing the component coefficient, `(1,1,1)`, fails at `n=4` on four copies
  of `FUUF`: `B_F=12`, `U0=0`, `R=0`, `C=2`, giving 10 instead of at most 8.
* Omitting branching while retaining the other full credits, `(1,0,2)`, fails
  on the cached `n=15` maximum witness: `B_F=55`, `U0=1`, `R=13`, `C=1`,
  giving 52 instead of at most 41.

The exact `n=7` counterexample to omitting `U0` is:

```text
FUFFFFF
FUUUUUU
FUUUUUU
FUUUUUF
FUUUUUF
FUUUUUF
FUFFFUF
```

Here `F` denotes forced and `U` denotes unforced.

Run:

```bash
python3 -m unittest discover -s analysis -p 'test_boundary_charge_reduction.py'
python3 -m analysis.bounds.boundary_charge_reduction --brute-max-n 4 \
  --exhaustive-maximum-n 6 --augmented-max-n 7
```
