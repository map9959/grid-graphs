# What sparse holes can buy through the interior

Consider a side at `x=0` and the candidate bar at `x=3`, on any
interval of `H≥4` rows. The first and last two bar sites are marked.
Reflect for the opposite side. The following bounds are for the
**physical marking**; the two ends need not be pitch profiles. The
two wings and their inward neighbors must be disjoint if using both.

**Separated holes.** Suppose holes on each candidate bar are at least
three rows apart. Let `u_i` count holes of wing `i` with an outer donor
(a mark at `x=1` in that row). In the original forced forest contract
the components, including isolated sites. For every hole add a test
edge from its bar component to the component at `x=4` in the same
row. Let `ρ` be the **joint graphic rank** of all these edges: the
number of successful unions, counting neither loops nor duplicates.
Then both bars can be made completely marked, with gain at least

```
ρ + Σ_i max(0,u_i-2).
```

In particular, on such an interval of an unrestricted maximizer, all
inward hole contacts already belong to their respective bar components,
and at most **two** holes per wing have outer donors. Even then the
holes can be removed without loss. This conclusion concerns the
actual component reaching each hole, not just the number of holes.

**Comparison to the objective.** For arbitrary intervals this gain
can be subtracted from the unrestricted upper. It beats the real
sector slack above `comb+1` if thirty times the gain exceeds
`k-26+3*((3k-13) mod 10)`. For aligned end rows at depths at most
nine and `n=3k+1≥103`, subtract the gain from the **comb** instead:
the repaired forest meets the [joint aligned-frame theorem](JOINT_ALIGNED_FRAME.md).
Thus any number of separated side holes is allowed in that exact
upper, even holes with marked guard neighbors on *both* sides.

### Why filling a hole does not cost two cycle repairs

Every vertical edge of the candidate bar is already forced. Its
holes, as well as its marks, are in a single tree. The two neighboring
columns `x=2,4` must be empty throughout: a mark there would be
diagonal to a bar mark in an adjoining row. Contract the bar path
to a root. The wing at `x=0,1` has one spoke from an `x=1` mark
to the root via the blank column `x=2` whenever the bar site is
marked. At a hole, that spoke is absent. At both ends the `x=2`
vertex is a root contact, not a free terminal.

Replace this wing by one valid even with **all** those spokes required.
Keep the marked bits of both pairs of end vertices at `x=0,1`. Require
that the replacement partition on those four vertices **and the root**
refine the original partition. These conditions suffice for gluing to
any exterior: the crossing edges at the two ends are unchanged and
the new forest cannot introduce any new identification of exterior
contacts. Each wing has price gain at least `max(0,u_i-2)`, proved below.
For now the restored spokes at the holes can be considered artificial.

Mark each hole. Its vertical edges already existed, and its outward
edge was included in the restored wing. Its only new edge is inward
to `x=4`. That site was an isolate or a leaf of the mark at `x=5`:
both its vertical neighbors are blank. The new wing partitions only
refined connectivity, so at least `ρ` of these inward edges can
be retained as independent joins. For each remaining cycle edge
unmark its `x=5` donor. This removes the old sole edge into the
corresponding leaf, after which the inward edge is harmless. Donors
lie off the required end words (and off both bars). With `m` holes
there are at most `m-ρ` deletions against `m` insertions. The final
spokes are all real forced edges; the resulting marking extends to
a spanning tree.

### Verifying the arbitrary-length wing price

Read two mark bits per row. Store the initial and current masks and
the partition on root, two retained initial vertices and two current
vertices. Reject a physical cycle at every join. At the last row
these are exactly the five comparison terminals. For each old price
key compare its score with the best fully wired key with the same
two masks and a refining partition. This is a component-by-component
comparison, not dominance of scalar maxima.

* Even dropping **every** intermediate spoke in the two-column model
  cannot improve the mark count against the best refining key.
  Keep two clean rows at either end. After 6 and 7 intervening steps,
  the whole clean and released prefix vectors recur with the same
  additive shift one. Closing both with two clean steps proves the
  zero-loss comparison for all heights.
* To price the outer donors, let the old transfer choose omitted
  spokes with a two-row cooldown; pay one extra objective unit when
  an omitted spoke has a marked `x=1`. The worst old excess over
  the best refining clean score is two. At 11 and 12 intervening
  steps the full paired vectors (including cooldown) repeat with
  equal shift. This proves the donor bonus at all lengths.

### Two-apart and clustered holes

If holes are merely **nonconsecutive**, a mark at `x=4` can occur
between two holes two rows apart. Clip these inward marks first,
at cost `e`. Each such mark leaves *two* isolated `x=4` sites at
the flanking holes: the corresponding `x=5` donors are forbidden
by diagonal exclusion. No two clips share one of these holes; two
`x=4` marks two rows apart would join each other as well as the same
side path, a cycle. Compute the join rank in the clipped forest;
then `ρ≥2e`.

On the wing side keep the actual third column instead of clipping it.
It sends a spoke to the contracted bar if **either** endpoint is marked.
The three-column transfer allows every nonconsecutive pattern of
missing bar marks. With the same boundary masks and partition refinement,
the clean wing gains at least `ceil(u_i/2)-2`. Its integer certificate
compares the two full normalized vectors after 13 and 14 steps.
Thus the net gain is at least

```
ρ - e + Σ_i (ceil(u_i/2)-2).
```

One may use the stronger two-column bound on a more widely spaced wing.
In particular even without any bound on the *number* of nonconsecutive
holes the aligned-end class scores **at most comb+4** with the two-row
end buffers. This pays the entire linear-coefficient gap, but not
necessarily the integer gap in the two-apart case.

There is a coarser consequence with **arbitrary** side words when
the two end words inside the rectangle are pitch. Let `g` count
adjacent pairs of holes on the two candidate bars (not on the outer
rim). Promote at most `g+4` sites: leave at most one hole in each
consecutive hole run and fill any missing second or penultimate
sites. Each insertion adds at most three units of cycle rank (if
four edges are new, the center was isolated). Each cycle can be
broken by deleting at most two unprotected marks: the forced stars
of the protected full bars and end teeth alone form a forest, so
some cycle edge lies outside these stars. Delete its marked owners.
Thus each promotion costs at most five net marks. The nonconsecutive
bound then gives `M≤comb+5g+24`. In particular `g=o(k)` suffices
for the comb **linear coefficient**, without assuming all the bar
vertices or their neighboring columns are clean.

### Checks and limits

At 103 a test with one hole per side had join rank two; the previous
whole-side tariffs at depths 3, 6 and 9 were all nonpositive. The
physical repair gained two, already exceeding the `7/6` real slack.
With sixteen holes and already-rooted inward donors, the join rank
was zero but the wing certificate alone paid twelve marks. Conversely
a single inward donor linked to the same north tree gives zero rank,
zero donor premium and zero gain in the replay. There is no positive
universal charge per hole. Neither the exact near-end pitch words nor
the sparsity conditions have been forced in every superior square.

```
python3 -B -m analysis.research_program.sparse_spoke_tile
python3 -B -m analysis.research_program.spoke_donor_price
python3 -B -m analysis.research_program.alternating_spoke_tile
python3 -B -m analysis.research_program.spoke_tile_crosscheck
python3 -B -m analysis.research_program.sparse_component_exchange
(cd lean && lake env lean GridGraphs/Geometry/SparseSpokeExchange.lean)
```
