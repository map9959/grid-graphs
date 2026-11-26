# Exact side 245: P(245,245) = 20,239

At score 20,240 the [two-gap case is impossible](BULK_AXIS.md).
In the one-gap case, transpose to put the isolate on the north arm
and [replace the perimeter](ONE_GAP_FRAME_EXCHANGE.md) by `0133` (any
other permitted one-gap word would also suffice). Of the 32 candidate
distances from the [previous ledger](SHORTEN_245.md), the only ones
left by root colors alone were **173, 179, 185, 191**.
Two further checked tests exclude them. The rail physically attains
20,239, so the unrestricted lower and upper bounds agree.
There is no prescribed donor, end mask, or shape of the interior.

Partition the interior into aligned `3 x 3` tiles. On every square
of four such tiles, exhaust the 36 mark bits under the physical local
charge and rooted-frame constraints in a six-site halo. Block each
listed quadruple and independently verify UNSAT. There are 169 base
catalogues and 66 additional catalogues to account for moving the
star, all DRAT-checked. Beyond the six explicit tile layers at each
end only the clipped axis types and phase matter. The physical replay
compares every axis stencil with side 119, including reflected types,
and checks the marks and directions on the perimeter. An isolate
outside a complete star stencil of a window does not incur a charge
inside it.

For each possible bulk axis, discard incompatible words. Propagate
across the square: a word can be deleted if no surviving word in the
adjacent block has the same two shared tile masks. This preserves
every physical witness at every deletion. In the batch CNF one global
star flag chooses the allowed location, and each selected quadruple
must belong to its appropriate catalogue. Adjacent blocks share
actual tile variables.

The decisive extra condition is connectivity. After removing the two
outer rings, no two distinct marked crop-boundary sites can be
connected: both had attachments to the same perimeter path.
Give north, east, south and west teeth distinct two-bit colors (one
fixed convention suffices for a corner tooth). Across each forced
crop edge both endpoint colors must agree. A component without a tooth
can use any color. This weaker test already yields:

| Forbidden deep center adjacency | North distances, step 6 | Result |
|---|---|---|
| Vertical | 5–191 | verified UNSAT |
| Horizontal | 5–95 | verified UNSAT |
| Horizontal | 101–155 | verified UNSAT |
| Horizontal | 161–167 | verified UNSAT |
| Horizontal, root colors and area modulo 2 | 173–191 | verified UNSAT |
| Horizontal, rooted crop and complementary face owners | 161–191 | independently verified UNSAT |

For the area test, join the isolate to its outward neighbor. The resulting
primal edges form a tree, and the remaining edges form the complementary
dual tree (including the exterior face). On a tree **any** prescribed edge
differences mod 2 admit vertex potentials: fix one vertex and propagate
along its unique paths. Thus the extra primal and dual potential clauses
in `tile_area.py` are necessary. Their UNSAT proof took 1,842,181 checked
resolution steps. In the other test each forced crop edge has one owner,
pointing toward its component's unique boundary tooth. Each bounded face
owns its edge toward the exterior in the complementary tree. This proof
took 2,904,429 checked resolution steps. Neither exclusion depends on a
converse for the respective relaxation.

```
python3 -B -m analysis.research_program.tile_case_ledger
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.tile_catalogue_check 0 12
python3 -B -m analysis.research_program.tile_star_catalogue --cert
python3 -B -m analysis.research_program.tile_family_board 245 2 --sat --colors=2 --dist=5:191
```

Survival is not attainment. For example a five-bit root-color run
selected 191 with 20,224 marks. Physical replay found 59,995 forced
edges on 60,025 sites, 32 components and cycle rank **2**. It is not
a spanning-tree witness. The actual rail replay is
`(20239,60023,2,60024,20239)`: one added edge completes its two
components to a tree with exactly 20,239 full-degree vertices.

## What transfers through a 42-site change of side?

For a straight track two tiles (six grid sites) wide, take as its end
state the two end tile masks and the color of every marked end site.
Each of the four colors is propagated on the **same** mark pattern.
One step selects a catalogued square of four tiles. Two marks at
Manhattan distance one or two must have the same color: their incident
forced edges connect them. Conversely these hops generate exactly the
connectivity among the marks. A three-site overlap is wide enough to
see every hop in one of the two pieces. In the boundary track assign
the marked boundary teeth their prescribed side color.

For either axis branch, either direction of travel and all 13 normal
position types, the Boolean endpoint relation at length `l` equals
the relation at `l+14` for every `l >= 11` tile steps. This is equality
of the sets of ordered colored endpoints, not just their sizes.
The verifier tests the first equality by computing complete relation
powers; composition proves the rest by induction. For example in
horizontal deep bulk, branch 1 gives 2,304 end states and 815,304
reachable pairs at lengths 10 and 24. In branch 2 the counts are
2,056 and 1,818,976 at lengths 8 and 22.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.colored_bulk_pump 1 --flat
# repeat for branch 2 and add --vertical for the other direction
```

This is a uniform shortening rule for the projected tracks only. With
the distance-five star at 245, the relaxation that links four corner
blocks by independently filled overlapping tracks across the central
`32:44` cuts is SAT in branch 1. Adjacent tracks cannot therefore
simply be filled independently to transfer the full-board exclusion.

There is an all-size barrier for the same idea even using every
overlapping track. Use the reference tile gaps `[7,18)` in rows and
`[62,73)` in columns. At 245 the independently checked assignments
satisfy all 4,471,055 clauses in branch 1 and all 4,502,147 in
branch 2, with the star at distance five. **This network relaxation
also admits that star at every side `245+42t`.** Keep the four corner
blocks, and lengthen each gap by `14t` tiles. Each bridge goes from
the tile just before a gap to the first tile after it, hence has
`12+14t` steps. Its longitudinal type is bulk throughout, its normal
type is unchanged, and no bridge contains the star. The four-color
relation at that length equals the one at 12 in all 13 normal types
and both directions. Restore the same corner masks and colors and
choose these track fillings. The interiors of the tracks are independent
in this test, even when their end tiles overlap.

Only the colors of marked end sites need be retained here. Every
forced connection between marks decomposes into one- and two-step
hops; each hop belongs to one of the pieces when the overlap is three
sites wide. Colors of unmarked sites can then be chosen from those of
their marked neighbors, or freely if there are none. This proves
feasibility of the network, **not** extendibility through the missing
two-dimensional overlaps. In particular a stronger size-independent
exclusion has to constrain those overlaps or use another invariant.
