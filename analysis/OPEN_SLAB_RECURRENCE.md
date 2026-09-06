# Rooted Open-Slab Recurrence Census

## Result

No exact-charge rooted open-slab recurrence occurs in the bounded straight-cut
family searched here. The exact census is produced by
`residue_two_open_slab_census.py` and committed as
`residue_two_open_slab_census.json`.

The two cross-family searches are:

```text
source -> target   observations   exact-charge observations   exact interfaces
A17 -> B20              330752                         3322                  0
B20 -> affine A23       535040                         3516                  0
```

For both transitions the minimum topology mismatch among exact-charge cuts is

```text
mask Hamming distance             0
rooted partition distance         0
forgotten-only components         1
cycle-excess distance             0
```

Thus the minimal obstruction is one hidden attachment component. It is not a
mask, visible partition, charge, or cycle-rank discrepancy. The component has
ports only in the opened three-column slab, so deleting that slab retires
information needed by a continuation. This is the concrete form of item 3 in
the missing attachment condition of `RESIDUE_TWO_REVISED_CONSTRUCTION.md`.

The self-family affine `A17 -> affine A20` pump is the positive attachment
control, but its increment is 72 U rather than the revised exact-charge
increment 71. Its minimum charge mismatch is therefore one before any
interface comparison. The direct `A17 -> A23` comparison is not a one-step
three-column slab transition and is recorded, but not searched, as a two-step
control.

No recurrence was implemented because there is no valid interface pair in this
finite family.

## Signature

Fix a top-down dual frontier of an `n` by `n` U-mask and open three consecutive
face ports starting at shift `s`. The rooted open-slab signature is

```text
(M, P, A, H, C, X).
```

Its channels are:

1. `M`, the previous-row U mask after deleting the three slab columns.
2. `P`, the canonical partition of retained dual frontier ports. Slot zero is
   OUT, so partition equality is rooted rather than equality up to an
   unmarked component permutation.
3. `A`, the canonical attachment partition on one token for every visible
   component followed by the three opened slab ports. This retains how hidden
   ports attach to visible rooted components.
4. `H`, the set of component labels represented only by opened slab ports. A
   composable interface requires `H` empty; otherwise deleting the slab forgets
   or retires a live component.
5. `C`, accumulated U cost minus the exact number of U cells in the deleted
   three-column prefix slab.
6. `X`, accumulated dual cycle excess.

For a source width `n` and target width `n+3`, compatibility requires the
source frontier mask, rooted partition, U cost, and cycle excess to equal
`M`, `P`, `C`, and `X`, respectively, and requires `H` empty. The full `A`
channel is retained in the signature so the closed-interface condition is
checked without projecting away slab-only components.

The implementation delegates frontier replay and lossless slab extraction to
the existing ranked recurrence tools. `RootedOpenSlabSignature` gives the
condition a named, immutable representation and the tests check its root and
cost normalization directly.

## Finite Scope

The certificate enumerates, without a beam or timeout:

1. The committed connected A17, B20, and affine A23 controls.
2. Every distinct D4 image of source and target independently, eight each.
3. Every nonempty, nonfinal source and target frontier depth.
4. Every legal shift of a straight three-column opened slab.
5. Every combination of those choices for the one-step pairs `A17 -> B20` and
   `B20 -> A23`.

Rows and columns are both covered because quarter-turns are among the D4
images. Reflections cover both directions along each cut. The artifact records
the input hashes, exact cardinality formula, per-channel zero counts, closest
samples, and a hash of the canonical claim.

This is not a global impossibility theorem. It does not cover bent or moving
cuts, slabs wider than three, interfaces that retain additional interior ports,
new controls, or the disconnected 333-U negative control after it seals a dual
component.

## Reproduction

```text
PYTHONPATH=analysis python3 -m analysis.transport.residue_two_open_slab_census
PYTHONPATH=analysis python3 -m unittest analysis/tests/transport/test_residue_two_open_slab.py
```
