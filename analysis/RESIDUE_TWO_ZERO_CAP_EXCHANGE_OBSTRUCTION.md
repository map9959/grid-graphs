# Residue-Two Exchange From the Residue-Zero Bottom Cap

## Scope

Let `m=3k`, `n=m+2`, and embed the proved residue-zero forced set `F0(k)` in
the top-left `m x m` square.  The target forced count is

```text
3k^2+7k.
```

The old bottom row is `.U.^(3k-2)`, so its forced cap is

```text
D_k = {(3k-1,c) : c != 1},       |D_k|=3k-1.
```

Deleting it leaves `3k^2-1` forced vertices.  Any replacement in `D_k` and
the two-row/two-column frame must therefore contain exactly

```text
(3k^2+7k) - (3k^2-1) = 7k+1
```

forced vertices.

## Rooted Bottom Topology

The complete residue-zero forced set has `3k-1` straight interval components.
Their forced-star incidence graph has `3k-2` singleton links and is a tree.
The bottom horizontal interval is a hub, not a leaf: deleting `D_k` leaves
`3k-2` straight components with only `2k-2` links, hence `k` incidence-forest
components.  A replacement cannot attach just once to one retained component;
it must replace the hub and reconnect the detached lower branches without
creating a cycle.

## Declared Three-Site Grammar

The first cap grammar keeps that topology as rigidly as possible:

1. Reinsert `D_k` unchanged, restoring the old rooted interval tree.
2. Use only the outermost row and outermost column of the new two-cell frame.
3. Permit every binary mask in each consecutive three-site packet.
4. Require every maximal selected outer run to meet the old tree support at
   at most one vertex.

The fourth condition is necessary for a stable leaf-insertion interface.  The
old support is connected, so two root attachments from one new interval star
would immediately close a cycle.  Ignoring interactions between distinct new
runs only enlarges the grammar, making the resulting capacity bound valid for
every singleton-intersection/tree-incidence realization in this class.

The outer L has `6k+3` sites.  Exactly `6k-4` are root-touching and seven are
root-free.  An exact two-state dynamic program over

```text
(previous site selected, root touches in current run)
```

exhausts all packet masks and gives maximum outer occupancy `3k+5`.  Including
the unchanged old cap, the entire grammar has capacity

```text
(3k-1) + (3k+5) = 6k+4.
```

This is short of `7k+1` by `k-3`.  Under `k -> k+1`, grammar capacity gains six
while the target replacement gains seven, so the interface loses one vertex
per three-column step.

## Checked Widths

| `k` | `n` | required replacement | grammar capacity | deficit |
|---:|---:|---:|---:|---:|
| 7 | 23 | 50 | 46 | 4 |
| 8 | 26 | 57 | 52 | 5 |
| 9 | 29 | 64 | 58 | 6 |

`check_residue_two_zero_cap_exchange.py` also verifies the source cardinality,
unit-cell condition, straight components, singleton star intersections,
tree incidence, forced acyclicity, and the retained-forest formulas.

## Required Non-Affine Topology

Any continuation of the residue-zero cap exchange must earn at least `k-3`
forced vertices from the inner frame layer or alter the old hub itself.  The
minimal topology is a two-layer interval ladder:

- the old bottom hub is replaced by a path of straight horizontal intervals;
- separate vertical singleton or short-interval rungs occupy the inner new
  row/column;
- each turn occurs through a shared unforced pivot, so forced components stay
  straight and no unit cell contains three forced vertices;
- each three-column successor packet adds one inner rung, reroutes one outer
  run attachment through it, and gains seven vertices rather than six;
- the complete replacement incidence graph connects the `k` retained forest
  components as a tree, with every pairwise star intersection a singleton.

This is not an affine endpoint surgery and not an outer-frame overlay.  The
next bounded grammar should enumerate one fixed base ladder at `k=7` and one
seven-vertex rung packet, with incidence-parent transport fixed in advance.
