# Separating the top and bottom crop ports: loss versus refund

Tested modifications of `Q_k`, not a universal grid upper bound. The
benchmarked quantity is **frame centers plus change in core count**. A
target successor needs `14k+25` of this quantity. Throughout, reserve a
fixed number of triples at both ends and keep them unmodified; the sides
and end/corner estimates from `MOVING_CORE_FRAME_RATE.md` then contribute
at most `6k+O(1)`. The paired top/bottom strips plus core changes must
therefore supply at least `8k-O(1)`.

### Adaptive removal of the connectors

The center in column `3j+2`, row `3j+2`, connects the rod on column `3j`
from below to the rod on column `3j+4` from above. Allow *any* subset of
these connectors to disappear. Keep each bottom root while its ports are
processed. At the shift to the next triple, either identify the new
top root with this same root, or allocate a fresh top root. Do not erase
any induced equivalences of the other frontier sites when a root splits.
This is a necessary cycle test for an attached frame even if some ignored
paths make true connectivity stronger.

At a fresh-root penalty c, maximize `frame-c*splits`. For c=0,1/2,1
the entire vector on the 516 attainable terminal states advances by exactly
`8-c` between blocks 4 and 5. The homogeneous block update commutes with
addition of constants, proving the same slope thereafter. Both the
union-find and explicit multigraph/DFS implementations give the same
vectors. Hence splitting for free reaches the desired raw frame slope of
8, but deleting one center per split leaves the **net** paired slope at 7.

### Coordinated relocation, shortening and promotion

Generalize the endpoints. Write `a_j=3j+u_j`. The top rod in column
`3j+1` ends at `a_j`; the bottom rod in column `3j` begins at
`a_j+2+g_j`. Relative to Q the top rod gains `u_j` and the bottom loses
`u_j+g_j`: the combined debit is precisely `g_j`. Choose modifications
only in a consecutive interior interval with fixed unmodified padding
(e.g. leave five triples unmodified at each end), so rods are nonempty
and these counts are literal. No periodicity of the choices is required.

Replace the old singleton in column `3j+2` by any subset of the interval
`[a_j+2,a_{j+1}+g_{j+1}]` in that column. This window stays at least
two rows from the ends of the two immediately neighboring rods. A
selected row at most `a_{j+1}` has a forced two-edge path to top rod
`3j+4`; one at least `a_j+2+g_j` has one to bottom rod `3j`. Keep track
of these actual connections, not just the number of promotions.

Rows in this subset separated successively by at most two belong to
one connected group. Two contacts of one group to the same rod force
a cycle: their contact paths run through distinct intermediate sites,
and the rod and the interval in the satellite column close the two ends.
Two groups that both span the two rods also force a cycle. Reject
those options. If exactly one group spans the rods, retain their
identification; otherwise permit a split. Other connections can be
omitted in an upper relaxation. Let `delta` be the number of selected
rows less `1+g_j`; it accounts for both the old singleton and the net
rod debit. Only the largest delta per split status is needed.

* With `u_j=0, g_j in {0,1}`, the joint choice of all trim bits,
  promotions and frame masks gives **net rate at most 7.5 per triple**.
  The 1,032-state vector at block six equals that at block four plus 15
  on every entry (independently regenerated). This allows both gained
  center count and lost count to accumulate, rather than examining an
  isolated promotion in a convenient background.
* With `u_j in [-2,2], g_j in [0,3]`, there are 20 endpoint types.
  Exhaust legal satellite subsets for each adjacent type pair. For each
  transition `x -> y`, let `s=1` if it splits the root, else zero. An
  integer potential with values in `[0,17]` verifies all **661**
  necessary-transition inequalities

      5*(2*delta+s)-3 <= potential(y)-potential(x).

  Summing gives `sum(delta+s/2)<=0.3m+17/10` on m triples. Add this
  to the independent frame certificate `frame-splits/2 <= 7.5m+O(1)`
  above. The splits cancel: **net paired score <=7.8m+O(1)**. With the
  two side strips, this gives a total upper of `13.8k+O(1)` versus
  `14k+25`. The linear deficit eventually applies on *both* parities.
  The coefficient is an upper bound, not a claimed optimum.

### Physical check and reproduction

In Q_4 delete the old satellite `(5,5)` and the bottom-rod tip `(8,6)`,
and insert `(7,5)`. Direct forest traversal verifies 68 centers instead
of 69, and confirms that top port `(0,7)` and bottom port `(13,3)` are
now in different components. Before the edit they were connected.
The script also exercises 24 local placements on the physical 14-square
and compares the separate frame transition implementations.

    python3 -B -m analysis.research_program.modified_crop

These exclusions rely on the stated rod columns and satellite windows.
In particular they do not resolve general crop rewrites, phase jumps
outside the tested ranges, or satellite centers spread across a wider
two-dimensional pocket.
