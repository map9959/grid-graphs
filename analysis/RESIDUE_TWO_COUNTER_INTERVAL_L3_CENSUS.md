# Counter-Interval L3 Corner Census

## Status

The counter-interval surgery remains an exact abstract parent/count identity,
but it has no realization in the declared natural corner grammar at `k=7,8,9`.
This is a bounded negative result, not a global obstruction to all coordinate
realizations.

## Exhausted Grammar

For `n=3k+2` and `L=k-5`, the checker exhausts:

```text
window                 rows 0..6, columns 0..6
C_k                     every horizontal length-L interval in the window
C_k centers             all must be new relative to the affine pattern
deleted centers         1..3 affine root/c=0-branch centers in the window
required deletion       (0,0) or (0,2), to destroy owner (0,1)
compensating additions  exactly as many as deletions, elsewhere in the window
non-counter edit cap    6
total edit cap           L+6
```

The equal deletion/addition counts make the final preserved count exactly

```text
(3k^2+6k+5)+L = 3k^2+7k.
```

Every enumerated choice is identified by the JSON tuple `(counter, deleted,
added)` and can be passed to `replay_choice`.  Validation is ordered as follows:

1. Exact target count.
2. No unit cell with three preserved vertices or a preserved diagonal pair.
3. Straight preserved components, with `C_k` an exact new component.
4. Injective transport of every affine component.
5. Acyclic forced star for each interval.
6. Pairwise star intersections of size at most one.
7. Exactly the affine incidence edges with `R_k-B_k` replaced by
   `R_k-C_k-B_k`.
8. Global forced-forest completion.

## Complete Counts

```text
k  n   placements  all-new placements  enumerated edits  realizations
7  23      42              17              5,098,725          0
8  26      35               7              1,868,139          0
9  29      28               4                945,400          0
```

All `7,912,264` edit choices fail at gate 2.  The JSON artifact records the
histograms and a replayable first violation for every width, including the
offending cell and its preserved offsets.

## Narrowed Next Surgery

The local horizontal counter cannot simply be laid into new corner vertices
and repaired by up to three root/branch exchanges.  A next symbolic surgery
must do at least one materially different thing:

1. Put the extra interval outside the `7x7` attachment corner.
2. Let the counter replace old preserved centers rather than being wholly new.
3. Permit deletions from the neighboring affine components implicated in the
   forbidden unit cells.
4. Produce the missing `+1` by lengthening an existing interval instead of
   introducing a separate counter component.

The grammar should not be enlarged automatically; one of these changes needs a
new symbolic parent/attachment specification first.
