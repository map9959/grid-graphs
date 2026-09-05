# Nonleaf-Spine Split-Bypass Obstruction

## Minimal Witness-Derived Operation

The five excluded two-leaf witnesses name exactly five nonleaf spines: four use
the horizontal root and one uses the moving vertical branch.  No choices are
added.

For a carrier endpoint ray `Q_k` of length `L=k-5` and its named parallel spine
`P_k`:

1. Orthogonally project `Q_k` onto `P_k`; this is the removed segment `D_k`.
2. The projection splits `P_k` into near and far straight intervals.
3. Keep the old carrier/spine singleton on the near piece as `alpha_k`.
4. At the far endpoint of `D_k`, place `L` centers perpendicular toward the
   carrier.  This is the equal-cardinality bypass `B_k`.
5. Require singleton owners `beta_k` between carrier and bypass and `gamma_k`
   between bypass and the far spine piece.
6. Translate the blocker by the direction already prescribed in the source
   endpoint-slide witness and require its unique replacement owner `delta_k`.

The nominal cardinality is exact:

```text
affine + |Q_k| - |D_k| + |B_k|
       - |blocker| + |moved blocker|
= affine + (k-5)
= 3k^2+7k.
```

## Five Types

The four root-spine carriers are:

```text
H:r2:c(3k-16), extend end;   blocker c=3k-13, move right
H:r2:c(3k-13), extend end;   blocker c=3k-10, move right
H:r2:c(3k-10), extend start; blocker c=3k-13, move left
H:r2:c(3k-10), extend end;   blocker V:c(3k-7):r2..3, move right
```

Their spine is

```text
R_k = H:r0:c2..(3k+1).
```

The vertical-spine type is:

```text
carrier V:c(3k-4):r6..9, extend end
spine   V:c(3k-2):r9..(3k-4)
blocker H:r(3k-9):c(3k-4), move down.
```

The JSON records every concrete old carrier/spine edge, blocker parent edge,
and physical attachment at `k=7,8,9`.

## Complete Obstruction

All five types fail exact count at every checked width:

```text
                 k=7  k=8  k=9
overlap failure    5    5    5
survivors          0    0    0
```

This is explained symbolically.  In every type the carrier and spine are two
lattice layers apart.  Let `q` be the far carrier-ray center.  The perpendicular
bypass starts at the projected spine endpoint and advances toward the carrier.
Because `L=k-5>=2`, its offset-two center is exactly `q`.  Therefore

```text
q in Q_k intersect B_k,
```

so the nominal additions overlap and the resulting set has at most
`3k^2+7k-1` vertices.  Additional overlaps at `k=8,9` only increase the deficit.
This proves the complete declared-grammar obstruction for every `k>=7`, while
the finite records replay the coordinate transcription.

The checker also implements the later gates for straight split components,
exact bypass and moved-blocker components, old-component transport, interval
star acyclicity, singleton intersections, retained parent edges, the declared
`alpha/beta/gamma/delta` owners, incidence-tree edge count, forced forest, and
insertion stability.  None is reached because exact count fails first.

Each record replays from

```text
(k, carrier, side, blocker, spine, prescribed blocker translation).
```

## Narrowed Next Topology

The bypass must not cross a carrier center.  The next symbolic topology is an
**offset spine bypass** with cardinality-neutral endpoint connectors:

```text
offset perpendicular core length  k-7
near connector leaf                    1
far connector leaf                     1
total relocated spine centers      k-5.
```

At `k=7` the core is empty and the two connectors remain.  The core is placed
one additional lattice layer away from the carrier; the connectors, rather than
core centers, must supply the singleton `beta_k` and `gamma_k` attachments.
This exact index/count specification must be settled before any coordinate
census.  No arbitrary shifts or extra edits are justified by the present
obstruction.
