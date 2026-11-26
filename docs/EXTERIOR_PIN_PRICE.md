# Pricing the exterior without seeing its marking

Use the [strict pitch frame](RESIDUE_ONE_PITCH_FRAME.md), with `s` known
solid columns (including the sides), height `H`, and left/right margins
`d₁,d₂`. Put `F=B-s-(R-t)-z`; the previously proved bound is
`3M ≤ n²+F-1`. The following price uses no measured exterior statistics:

```
F ≤ 4n - s - ceil(2(s-1)/3) - D(d₁,H) - D(d₂,H).
```

Here `D(d,H)=max(0,dH-3U(d,H)-2d)` and `U(d,H)` is any upper
on the number of marks in `d` free columns adjoining an `H`-site
full bar. One may also use `D(1,H)=H` and `D(2,H)≥H-2`.
The [all-depth full-bar tariff](FULL_BAR_EXCHANGE.md) works at any
margin. At small margins the finite strip transfer is sharper.

**Why the pins pay even when widely spaced.** On each end of the
frame, take one triple centered at each end tooth, including the
lateral leaf just outside each extreme tooth. Both extra leaves are
unmarked by diagonal exclusion. In a window of two or three triples,
follow the actual cap from the pitch row out to the board edge.
The local bill is:

* missing marks in the final rim word;
* run starts after the first cap row (predecessors toward the frame
  and west), ignoring the leftmost column;
* isolates in the interior columns, including final-row isolates.

Such starts are not among the `t` deductible runs, and the isolates
are not ports. Each charged item is in `4n-B`, `R-t`, or `z`.
At either end the bill is at least **the number of distinct terminal
classes minus one**, for windows of two or three triples, at any cap
depth. The transfer starts with each tooth joined to its two leaves,
the teeth mutually separate. Every row adds actual forced edges and
rejects a cycle; it retains the partitions of the permanent tooth
labels and current frontier. One pending bit per interior column
suffices for its preceding site's isolation charge. The first free
word is any subset of the pitch centers. The final word is free.
Reachability at bill at most `k-2` proves the price for `k=2,3`,
since the number of classes is at most `k`. Rust visits 30 and 924
states, respectively; the independent Python search also distinguishes
the identities of the surviving classes. At **four** triples all four
classes can survive at bill two, so extending this local assertion
to arbitrary window width would be wrong.

Cover the ordered tooth indices with windows `[1,3],[3,5],...`,
truncating the last window if necessary. Use a second cover starting
with `[1,2],[2,4],[4,6],...`. Consecutive windows in each chain
share a terminal. Therefore the sum of their class counts minus one
per window bounds from above the class count minus one on the whole
chain. Do this independently in the two caps. Joining just the `s`
known pairs is a forest, so the two cap class counts sum to at least
`s+1`. Each chain thus bills at least `s-1`; a site occurs at most
three times across the two covers. This proves the rounded pin price.
No unpinned tooth pair was identified in the join.

**Why the wings can be added.** A lateral `H×d` wing has an empty
first column beside the full bar. Call `I` its marked short-end
incidences, `B_w` its marked outer-side incidences, `R_w` its runs,
and `c_w` its components. Its ledger is
`B_w=3M_w-dH-I+R_w+c_w`. At most `I` runs extend out of the wing.
At most `H` components touch frame ports inside the wing, and at most
`2d` others escape by its short ends. Thus, after subtracting wholly
contained runs and closed nonport components, the remaining outer-side
benefit is at most `3U-dH+H+2d`. This proves the wing debit. At depth
two, marked rim sites must be three apart (otherwise they reconnect
through the side bar); all but at most two are whole singleton runs.
Wing debits use no starts or isolates of the cap windows.

The implementation can leave either wing unpaid and use its remote
area instead: its `d-1` columns more than one step from the frame
cannot be covered by a deductible run or a port. Each other run
covers at most `3n` sites with its stars, and uncovered sites are
isolated. When also charging cap windows restrict this area to the
middle `H-2` rows so a cap run cannot cover it. Disjoint forced
corner omissions can be added, skipping any corner whose candidate
holes already enter a paid rim segment.

**Consequences.** At side 103 with margins four and five, a score of
3647 is impossible at every vertical placement in these cases:

| Known pins (at least) | Frame height (at least) |
|---:|---:|
| 2 | 65 |
| 10 | 59 |
| 20 | 47 |
| 32 | 35 |

This also yields an all-size obstruction. The complete normalized
wing vectors agree at heights 7 and 10 for margin four, and 11 and
13 for margin five, with increment three in both cases. Checking the
prefix and iterating gives `U(4,H)≤H+2`, `U(5,H)≤3H/2+3`. Thus the
two wings bill at least `3H/2-33`. For every `n=3k+1≥1000`, a
frame with those margins and `H≥n/2` puts the score **strictly below
the comb**, even if the only known pins are the two sides. Lean
checks the final integer comparison. On the ordinary phase, e.g.
the 33-pin comb frame at 103 with margins three and three, this
geometry-only method gives 3653 and does not improve the existing
unrestricted 3647. No placement theorem forces the off-phase margins.

For aligned margins of three and end depths at most nine, the
[joint cap and wing price](JOINT_ALIGNED_FRAME.md) now improves the
side-103 bound to 3646.

```
rustc --edition=2021 -O analysis/research_program/pin_cap_rank.rs -o target/pin_cap_rank
target/pin_cap_rank 3
python3 -B -m analysis.research_program.pin_pair_tariff 3 2
python3 -B -m analysis.research_program.exterior_surface_bound
(cd lean && lake env lean GridGraphs/Geometry/ExteriorPinPrice.lean)
```
