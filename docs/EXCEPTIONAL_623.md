# P(623,623) = 129,967

With `k=207` the [unrestricted residue-two bound](RESIDUE_TWO_CLASSIFICATION.md)
is `U=129968`. Equality would require either the normalized one-gap
chart or an ordinary two-gap bridge. Both cases are empty. The rail
attains `U-1`.

**One gap.** The [uncapped coupled-mask transfer](UNCAPPED_ONE_GAP_623.md)
excludes deficit 1,062 with both possible deep axes and every isolate
distance `5,8,...,617`. Width-three bands jointly process neighboring
cuts on identical masks with one physical forest partition. Alternating
the directions propagates the shared mask restrictions; emptiness is
conclusive without assuming a bound on the number of connections.

**Two gaps.** Normalize to frame `0011`, ordinary north exit, root at
NW. The [uniform end exclusions](CORE_413_UNIFORM.md) require distance
at least 308 from both north corners. Only `d=308,311,314` remain;
the [deep-bond reduction](TWO_GAP_EXIT_TRANSFER.md) forbids horizontal
deep center bonds. These are not one-gap charts.

Use the actual two-gap physical charge tables on a local rectangle
consisting of the 6-by-6 physical sites of a plaquette and a four-site
halo, clipped at the real board boundary. Use zero-charge patches,
the guarded perimeter exit charge, the enforced compass arcs and turn
sheets, matching, and the `0011` frame. Orient each perimeter path
towards its root or exit; ordinary north teeth other than the exit
point outwards. Project only the central four masks. To certify coverage,
block every listed quadruple on those 36 mark bits, then run CaDiCaL
and verify UNSAT with `drat-trim`. Only these **local** SAT exclusions
are used in generating the new catalogues. The full-square exclusions
use strip dynamic programming.

Two positions may reuse a table when their translated boxes have
identical clipped coordinate tags, including reflected tags (for both
patches and stars), frame bits and perimeter parents, and the same local
exit guard. All coordinates are on side 623 itself. Each exit used
74 local data types, or 79 with the deep-axis filter; the local CNF
and ordered projection bits gave 35 distinct coverage proofs across
all three exits. The replay regenerates and checks those proofs without
saving board-sized proof files.

**Bridge partition rule.** The unique two-tooth crop component has the
ordinary north exit as one endpoint and a tooth of the long arc as
the other. Omit the exit's *attachment to the common root*, not its
mark or any forced physical edge. Every full marked crop component now
has exactly one remaining tooth. Thus the same physical-strip forest
test is necessary with this one omission. The site is `(d-1,1)` in
zero-based `(x,y)` crop coordinates. A positive bridge control with a
marked north-to-south line accepts the designated endpoint and rejects
a one-tile shift of the exception.

| north exit `d` | tile `q` | first empty width-three vertical band starts at |
|---:|---:|---:|
| 308 | 102 | 101 |
| 311 | 103 | 102 |
| 314 | 104 | 103 |

The starting columns are after propagation; no isolated band with
unconstrained neighbors is claimed impossible. The independent
opposite-half-forest checker found the same seven contradictions
(four one-gap ranges plus these three exits).

**Construction.** Independent physical rail replay returned
`(129967, 388127, 2, 388128, 129967)`: the forced forest has two
components, and one extra edge gives a spanning tree of all 388,129
vertices, with 129,967 full-degree sites.

```
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.side623_coupled_ledger --drat
(cd lean && lake env lean GridGraphs/Geometry/CoupledMaskSupport.lean)
```

Lean checks the general support-deletion invariant and endpoint
arithmetic. It does not replace the catalogue checks, DP or tree
replay. The next open exceptional side is 665; the specific empty
side-623 frontiers do not prove that enlarging the board preserves
emptiness.

The [insertion-closure replay](FOLDED_STRIP_ENLARGEMENTS.md) now proves
that the two-gap exclusions extend to all enlargements; only part of
the one-gap proof extends.
