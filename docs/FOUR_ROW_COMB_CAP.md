# A four-row cap: exact side 46 and a growing residue-one lower bound

`P(46,46)=753`. The previous construction gave 752. The unpooled
certificate gives the unrestricted upper `2354221867/3125000 < 754`.
`analysis/research_program/forest_46.txt` is a physical 753-site witness.
Union-find accepts all 2112 forced edges, and four components complete
to a 2115-edge tree with 753 full-degree vertices.

For **every** `n=3k+1`, `k>=3`, the same family gives

    P(n,n) >= 3k²+5k+floor((3k−13)/10).

Here the floor is an exact score of the constructed family, not a proposed
unrestricted upper. One may retain earlier lower bounds when stronger.

## The width transfer

The [unbounded rail-seam theorem](UNBOUNDED_RAIL_SEAM.md) now gives
the matching upper with arbitrary interior and exterior marks whenever
two opposite boundary strips of depth six each contain a rail-profile
row (or, after transposition, column).

Use a full top row, an empty row, `n−8` identical rail rows (marks at
`0,3,...,n−1`), four freely chosen cap rows, an empty row and a full bottom
row. Before processing the cap, the upper fixed graph is a tree: the rails
are paths with disjoint teeth, attached once to the full top bar. Every
site in the last rail row belongs to this component. The bottom bar and
its teeth in the penultimate row form another tree. Contract these two
trees to two distinct terminal vertices.

Process one cap column at a time. Retain its four marked bits and the
connectivity partition of the four sites and both terminals. Add a forced
edge to the upper terminal if the first bit or the fixed rail site is
marked; add an edge to the lower terminal if the last bit is marked.
Add all forced vertical edges in the column and horizontal edges to
the previous column, rejecting a transition whenever an edge joins
vertices already connected. Components no longer on the frontier can
be forgotten. The quick diagonal checks also reject only forced unit
cycles. No test assumes a particular cap orientation or a particular
number of components.

Inductively the partition contains all connectivity relevant to future
columns. Maximizing the number of marked bits per state therefore gives
an attainable cap maximum. The first column has a special initialization;
subsequent transitions depend only on column index modulo three.

At widths **10 and 40**, the *entire* vector of maxima over reachable
states is identical up to addition of **33**, with the same 63 states.
The phase agrees and the maximum update commutes with a uniform score
shift. Applying the same updates any number of times proves that adding
30 columns adds 33 to the cap maximum at every width from 10 onward.
At the ten starting widths `n=3k+1`, `k=3,...,12`, the computed cap
score is `3k+5+floor((3k−13)/10)`. This expression has precisely that
period increment. Adding the `2n+(n−8)(k+1)` fixed sites proves the
stated unrestricted lower bound.

```
python3 -B -m analysis.research_program.comb_cap_transfer 46 4
python3 -B -m analysis.research_program.comb_cap_transfer --period
python3 -B -m analysis.research_program.patch_square --replay 46
```

## Exact side 49

At `k=16` the cap gives 851 sites, forcing 2399 acyclic edges. A single
joining edge gives a spanning tree with 2400 edges and 851 full-degree
vertices. The unrestricted unpooled upper is `85167992073/100000000`
(including residual allowance `2671/100000000`), strictly below 852.
Thus `P(49,49)=851`; the rational certificate alone rules out 852.

```
python3 -B -m analysis.research_program.comb_cap_transfer 49 4
python3 -B -m analysis.research_program.patch_square --replay 49
```

## The same upper even with arbitrarily many five-row seams

Keep the two outer bars, their empty neighboring rows, and the four
free bottom cap rows. In the intermediate rail region require its
first and last rows to be the usual `0,3,...,n-1` rail profile.
**Any number of disjoint bands of up to five completely free rows
may replace straight rail rows, provided consecutive bands are
separated by at least one ordinary rail row.** Marks in the bands
and the bottom cap may be optimized jointly. The exact maximum
number of designated marks is still the four-row comb formula.

For a band of height `h`, divide its columns into modules by the
nearest rail. Pad the two outside modules to width three with
unmarked sites, which add only leaves. Include the neighboring
ordinary profile on either side of the band. Consider just the
forced subgraph within such a `3 x (h+2)` rectangle. The following
are the exact maxima in its `h` free rows, according as its two
end rail centers are disconnected or connected **within this
module**:

| `h` | disconnected | connected |
|---:|---:|---:|
| 1 | impossible | 1 |
| 2 | 0 | 2 |
| 3 | 2 | 3 |
| 4 | 3 | 4 |
| 5 | 4 | 5 |
| 6 | 6 | 6 |

`python3 -B -m analysis.research_program.shallow_seam` checks the
table by enumerating three-bit rows and testing the forced edges
by union-find. No boundary conditions are imposed on the lateral
edges. For heights at most five, each module has at most `h` marks,
and an unconnected one loses at least one. The last line explains
where this local argument stops.

Contract each ordinary rail segment and its teeth. Retain a link
across a module exactly when its two centers are locally connected.
These links together with the caps form a forest: they can be
realized by paths with disjoint interiors in the old forest after
contracting the ordinary rail segments. All other connections in the
free bands may be discarded for this argument. Straightening every
band corresponds to inserting all missing links. Do them one at a
time. Each gives at most one cycle, which can be broken by deleting
**one mark from the free bottom cap**:

* The straight rails joined to the top bar alone form a tree, so
  any new cycle traverses the bottom cap and must enter it from a
  rail center. The first cap row can mark only rail columns, by
  diagonal exclusion against the last ordinary rail row.
* If the cap path reaches the bottom bar, the edge into its empty
  neighboring row has a single marked owner, in the cap. Otherwise
  the path must change columns before returning to another rail.
  At the first horizontal edge, either that edge has only one
  marked endpoint or the preceding vertical edge does: three
  marks along the turn would include a diagonally adjacent pair.
  In the second case its marked endpoint is the cap site at the
  turn. A horizontal first edge directly after entering from a
  marked rail center cannot have both endpoints marked.

Deleting the sole cap owner deletes the edge and creates no cycle.
There are no more deletions than missing links, already paid for by
the mark deficits of the unconnected modules. Filling straight
rails therefore gives an ordinary four-row-cap forest with at least
the original score, which proves the upper. The original comb attains
it. This is a construction-class theorem, not an unrestricted upper.
