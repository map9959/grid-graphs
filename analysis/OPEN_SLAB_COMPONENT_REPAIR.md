# Open-Slab Component Repair

## Result

The closest exact-charge interfaces do not admit a closed repair in the
bounded local neighborhood searched here.  No recurrence candidate is
implemented.

The exact minimum repair at these interfaces is:

```text
additional retained dual ports    1
additional U cost                 0
```

The extra port is the sole frontier occurrence of the forgotten component.
Retaining it makes the interface closed; deleting that one extra token from
the wider projected partition recovers the source partition exactly.  The U
mask, normalized cost, and cycle excess are unchanged.  Because the target
pattern is not edited, its verified dual connectivity and forest completion
are also unchanged.

This is a wider state space, not a recurrence on the original interface.  In
particular, the affine A23 sample has 335 U cells, not the revised 333-U target;
"exact charge" here refers to the normalized depth-2 interface channel in the
committed census.  The result therefore does not establish the revised
residue-two recurrence.

## Samples

The eight closest records in `residue_two_open_slab_census.json` reduce under
reflection to three concrete searches:

```text
transition       depth  slab  representative orientations                 multiplicity
A17 -> B20           2     0  rotate_90 -> rotate_270                                3
A17 -> B20           4     2  rotate_180 -> rotate_180_reflect_lr                    2
B20 -> A23           2     0  rotate_90 -> rotate_270                                3
```

Every representative starts with mismatch vector

```text
(mask, partition, forgotten, charge, cycle) = (0, 0, 1, 0, 0).
```

The target U counts are respectively 250, 250, and 335.  Each unedited target
is dual-connected and forest-completable.

## Balanced Exchanges

For each representative, the search exhausts all balanced U/full exchanges of
sizes zero, one, and two in the oriented box

```text
rows       0 .. depth+2
columns    slab_start .. slab_start+5.
```

Thus the target U count is invariant.  Every candidate is replayed through the
complete target, so a counted survivor is dual-connected; survivors are also
checked independently for forest completion.  The straight interface is then
re-extracted at the original depth and slab position.

The exact census is:

```text
class                         size  tested  connected  forest  exact interface
A17->B20 depth 2                 0       1          1       1                0
                                  1     209          0       0                0
                                  2    9405          1       1                0
A17->B20 depth 4                 0       1          1       1                0
                                  1     392          0       0                0
                                  2   34398          0       0                0
B20->A23 depth 2                 0       1          1       1                0
                                  1     209          0       0                0
                                  2    9405          1       1                0
```

There are 54,021 explicitly replayed representative candidates, corresponding
to 127,272 candidates before reflection reduction.  In both depth-2 classes,
the only connected two-for-two exchange changes

```text
U -> full    (0,1), (0,2)
full -> U    (1,0), (2,0),
```

and worsens the forgotten-component count from one to three.  No one-for-one
exchange remains dual-connected.  At depth 4, no one- or two-exchange candidate
remains dual-connected.

## Bent Interfaces

The port census is broader than a geometric one-step bend: with the mask slab
and charge normalization fixed, it exhausts every three-element subset of the
entire non-root target frontier as the forgotten face-port set.  Consequently
any equal-width bent selection at that frontier is included.

```text
class                         3-port sets  closed sets  exact source interfaces
A17->B20 depth 2                      969            0                        0
A17->B20 depth 4                      969            8                        0
B20->A23 depth 2                     1540            0                        0
```

The eight closed depth-4 reroutes do not reproduce the source rooted partition:
the source has one repeated visible block while each closed reroute has only
singleton blocks.  Hence closure alone does not yield a recurrence.

For minimality, the script also exhausts every two-element forgotten port set,
equivalent to retaining one additional target port.  The natural repair keeps
the original straight slab except for the forgotten component's sole slot:

```text
class                         original hidden  wider hidden  extra retained
A17->B20 depth 2                    1,2,3           2,3               1
A17->B20 depth 4                    3,4,5           3,4               5
B20->A23 depth 2                    1,2,3           2,3               1
```

Each wider interface is closed and projects to the exact source partition when
the extra token is removed.  Zero extra ports is impossible by the exhaustive
three-port census; one is sufficient by the displayed witness.  No cell is
changed, so the exact additional U cost is zero.

This certificate is finite.  It excludes only balanced exchanges through size
two in the stated boxes and arbitrary port rerouting at the fixed closest
frontiers.  It does not exclude larger edits, cuts visiting other frontier
depths, or a recurrence carrying the extra port through a subsequent step.

## Reproduction

```text
PYTHONPATH=analysis python3 -m analysis.transport.open_slab_repair_search
PYTHONPATH=analysis python3 -m unittest analysis/tests/transport/test_open_slab_repair.py
```
