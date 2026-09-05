# Prefix component ledger

For a width-`n`, height-`r` processed rectangle, let `F` be the forced vertices
and assume the forced-edge graph `H` is a forest.  Write `c_H` for the number
of components of `H`, `c_F` for the number of components of the induced graph
on `F`, and `Q_F` for the rectangular boundary deficiency of `F`.

`grid_component_reduction` gives

```text
3|F| + c_F + c_H = rn + Q_F.
```

Consequently the accumulated row charge has the exact signed form

```text
sum (n + 3 - 3|F_row|) = 3r - Q_F + c_F + c_H.       (1)
```

The subtraction-free form of this identity is now kernel-checked as
`grid_prefix_component_ledger`.

The coupled discovery state records `Q_F` incrementally as
`forced_boundary_deficiency`.  Active plus retired partition blocks are exactly
`c_H` and `c_F`.  Exhaustive transition replay verifies (1) through width six.

At terminal depth `r=n`, the desired accumulated charge of at least four is
therefore exactly

```text
3n - Q_F + c_F + c_H >= 4.
```

Equivalently, with `U` the complement of `F` and total square boundary
deficiency `4n`, this is

```text
Q_U + c_F + c_H >= n + 4.
```

Thus the prefix ledger removes coefficient discovery from the induction but
does not itself prove the terminal inequality.  A successful frontier argument
must bound the terminal boundary/component expression, most likely using a
nonlinear interval-packing invariant.  Finite interval-potential tables remain
falsification evidence only and are not part of the Lean proof.
