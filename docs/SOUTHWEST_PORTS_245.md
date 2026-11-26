# Southwest completion excludes the 59 recorded nonshortenable port pairs

**No side-245 one-gap upper witness can have any of the 59 right-band
end-mask pairs certified in [the shortening test](SHORTEN_245.md).**
This is a conditional exclusion on the *end marks*. It does not
assume that the rest of the board looks like the archived donor.
In fact the exclusion holds with the old regional forest constraint
and only local constraints in the new southwest; it is not necessary
to impose acyclicity of routes through the added region.

## Quantifiers and model

Normalize the star to `(2,d)` by transposing the whole board when
the original star is on the west arm. Keep all 16 frame selectors:
the eight original north-gap frames and their eight transposes.
The sole 72 charge can be at any of the 32 distances `d=5,11,...,191`.
This represents all **64 physical sites in every original frame**.

For each start `s=102,...,160`, read just the marks in columns
`143..244` of rows `s` and `s+78` from `long_quarters_5_5.gz`.
A selector for `s` implies those 204 signed literals. At least one
selector must hold. No arrow, path partition, or intervening mark
is taken from the sample. Both the end coordinates and the mark
values matter; arbitrary translations or new end masks are not
covered by the theorem.

The original regional model left out `[102,236] x [8,142]`. The new
model puts **all 18,225 omitted vertices** into the same grid. Each
must be covered by a mark on its closed unit neighborhood. Every
`3 x 3` patch has zero charge, including patches crossing the old
fringe, and every star except the chosen isolate has zero charge in
the SE rooting. The full-board test keeps forced-edge ownership,
the perimeter arrows, and turn-sheet constraints on the common forest.
All these are necessary for a score of 20,240.

The split formulas restrict the allowed port selectors, but **each
one keeps the entire star disjunction**. Independent `drat-trim` checks:

| Starts | Frame/site/start combinations | Resolution steps |
|---:|---:|---:|
| 102–111 | 5,120 | 4,277,136 |
| 112–121 | 5,120 | 7,080,879 |
| 122–131 | 5,120 | 16,820,162 |
| 132–141 | 5,120 | 6,422,609 |
| 142–149 | 4,096 | 24,915,067 |
| 150 | 512 | 14,825,963 |
| 151–160 | 5,120 | 16,537,142 |

The union has `59*32*2*8 = 30,208` members. Checking only the
original donor's frame or distance would not prove this statement.
There is a geometric consequence: the 59 pairs occupy **disjoint**
sets of vertices, since their first rows are `102..160` and their
second rows are `180..238`. A putative upper witness must therefore
change **at least 59 marks or empty sites** relative to the donor
among those 12,036 sites alone, in the normalized coordinates.
The full CNF before splitting has 359,308 variables and 6,156,937
clauses, SHA-256 `cd5366fad219c70f73f7d2baf43a2d6c6fc8c2eb551f47ee1a1cb6bc623215e4`.
The ledger rebuilds each batch from that base and checks the actual
selector-to-coordinate clauses, the southwest coverage clauses,
the batch digests, and disjoint coverage of the Cartesian product.

```
python3 -B -m analysis.research_program.southwest_ports_ledger
# full forest: 59 mask pairs x 64 sites x 8 frames = 30208 excluded
# add --drat to repeat the proof checks
```

To regenerate the common input and an individual batch:

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.southwest_ports 5 191 102 160 -3
python3 -B -m analysis.research_program.sw_port_batch 102 111 5 191 240
```

## What is needed from the rest of the board?

**Separate test of the local extension.** Keep the common acyclic
three-quadrant-plus-rim region, but drop every turn-sheet constraint
whose three vertices do not all lie in that old region. Thus a
directed cycle using the southwest need not lift to two compass
sheets. Still cover every southwest site, assign every forced edge
one direction, check the outdegree/star charge at each vertex and
the patch charge at every origin, including across the old fringe.
These are joint local constraints on the same marks and arrows,
not separate marginal choices. In this weaker model all 30,208
combinations are again UNSAT:

| Starts | Combinations | Checked resolution steps |
|---|---:|---:|
| 102–121 | 10,240 | 5,960,849 |
| 122–141 | 10,240 | 8,504,093 |
| 142–160 | 9,728 | 18,392,640 |

The base has 5,713,057 clauses, 443,880 fewer than the full test,
with identical mark and selector IDs. SHA-256:
`c0ea2ed713e5753dce2028cc3552efc9c186a6fc36794acfe0d1e68528b95b7c`.
Regenerate with `southwest_ports 5 191 102 160 -3 2`, then run
`sw_port_batch a b 5 191 300 1` for each listed interval. These
three proofs alone suffice for the exclusion.

The original donor is a checked forest on the *northern/eastern*
domain with the port at 150. Conversely, there is now a checked
forest on **all rows 101 through 244** with that same pair: 35,280
vertices, 35,250 forced edges, 30 components, no cycle. The physical
replay checks the permitted southern frame, all visible charges and
coverage of every southwest vertex. So the recorded pair and the
southwest constraints are compatible on this southern rectangle by
itself. It is compatibility with the rest of the one-gap conditions
that fails. These two regional forests are not a common witness.

```
python3 -B -m analysis.research_program.southwest_port_strip 150 150 -1
```

There is slack in the negative result. For start 150 a second checked
proof drops **62 of the 204 fixed bits**. Only 71 specified sites at
each end remain: any full witness agreeing at those 142 sites is
excluded regardless of the other 62 values. The retained requirements
were extracted from the trimmed proof core and a fresh `drat-trim`
check was made against the weakened CNF (SHA-256
`859a58ebab674b0a4e723de2f9f6b5119ac9a0061d2e084986f6c9abb6899234`).
The 142 sites are sufficient, not claimed minimal.

For starts `104,107,...,158` a different weakening retains **only the
end bits common to all five archived regional forests**. The 19 partial
pairs fix 190–195 of their 204 bits. Their 36-step strip test is UNSAT
(`star_strip_interface` phase 2, consensus mode, SHA-256 `834fd15a27c9e027e9aeffea0e4c79622653f0050aa77905cb21902fbeea1426`).
The side-245 southwest-local completion is also UNSAT in three checked
batches, retaining every star and frame: starts 104–119, 122–137 and
140–158, step three in each. Reproduce with `southwest_ports 5 191 a b
300 2 1`. Thus all five donors are covered at these starts, and the
exclusion covers 110,080 placed binary end words when the unspecified
bits are varied independently. Not every such word need occur regionally.

This removes an explicit obstruction to using the side-203 transfer,
not all possible obstructions. No star site is excluded *without* a
port hypothesis by these batches; a different nonshortenable end
pair, or a different construction, remains possible. The unrestricted
bounds are still `20239 <= P(245,245) <= 20240`.

Subsequent results: the [bulk-axis proof](BULK_AXIS.md) eliminates
the entire two-gap case at 245, and [perimeter exchange](ONE_GAP_FRAME_EXCHANGE.md)
reduces one-gap existence to a single frame and 32 north distances.
The subsequent [port-free tile certificates](TILE_CASES_245.md)
exclude that disjunction, proving `P(245,245)=20239`.
