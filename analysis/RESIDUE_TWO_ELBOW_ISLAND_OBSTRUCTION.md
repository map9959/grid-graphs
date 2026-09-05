# Residue-Two Minimal Elbow/Island Classification

## Grammar

The core is the `3k x 3k` interior of the `(3k+2)`-square. A lower and an
upper monotone staircase wall divide it into a vertical-rail domain, one
bounded-width island, and a horizontal-rail domain. The finite state is

```text
(row mod 3, lower wall mod 3, width, exterior phases,
 island orientation, island phase).
```

Both wall advances lie in `{0,1,2,3}`. In one packet each wall advances by
three. Noncrossing requires the width to remain in `{1,2}`. Width one is the
smallest strip that can change one center per packet, exactly the rate needed
to repair the preceding `k-2` deficit. Width two is the least enlargement
that permits a genuine `1 -> 2` or `2 -> 1` elbow. The island phase is one of
the two phases unequal to the host row or column phase.

For each transition the checker inspects every unit cell meeting either wall.
It rejects three preserved centers and either preserved diagonal pair. This
leaves a finite transfer automaton: 56 phase-free noncrossing wall cycles and
1,044 phase-decorated local packet paths. There is no board search.

## Incidence And Caps

The island and the two exterior domains own disjoint preserved-center sets.
Their forced supports include each center and all of its grid neighbors. A
singleton articulation means that the island forced support intersects the
combined exterior support in exactly one physical vertex.

The cap checker contracts the core forced forest and runs the existing exact
max-plus perimeter automaton. Its state retains active core components, the
first and current perimeter vertices, connectivity partition, and previous
occupancy. A union inside one partition block rejects a forced cycle,
including at final perimeter closure.

Three cap arcs are not inferred from the number of occupied boundary runs.
They are the three cyclic ownership arcs on the inner boundary: one vertical
domain arc, one island arc, and one horizontal domain arc.

## Complete Finite Result

Of the 1,044 local paths, 513 have valid unit cells and forced-forest cores at
all of `k=7,8,9`. Exactly 56 have three stable ownership arcs. None has a
singleton articulation. The smallest island/exterior forced-support
intersection has size four.

Even if singleton articulation and the three-arc requirement are dropped, the
best count is

```text
core       = 3k^2 - 2k + 1
island     = k
cap        = 8k + 1
total      = 3k^2 + 6k + 2.
```

The totals at `k=7,8,9` are `191,242,299`; successor gains are `51,57`, hence
the stable gain is `6k+9`, still one below `6k+10`.

Imposing exactly three cap arcs lowers the best class to

```text
seam correction = 0
island centers   = k - 1
cap              = 5k + 2
total            = 3k^2 + 5k + 2.
```

Its cap counts at `k=7,8,9` are `37,42,47`. Its island/exterior intersection
sizes are `17,20,23`, not one. Thus no target family and no parent incidence
tree survive this grammar.

## Scope

This is complete for two noncrossing net-three walls, width states `{1,2}`,
one alternate row/column island phase, and arbitrary perimeter caps accepted
by the forced-forest cap automaton. It does not block lower L2 beyond the
declared finite grammars. In particular it does not exclude width at least
three with a blank buffer and endpoint-only attachment, branching walls,
multiple controlled articulations, or nonmonotone domain walls. The next
topology is therefore a buffered width-three island or a branching three-wall
junction, not another width-one phase exchange.
