# No-pitch junction debit and the rank transported through a cross

For the two-direction repair, the additional empty-stub price and
the exact fractional obstruction see [orthogonal cut rank](ORTHOGONAL_CUT_RANK.md).

Use the [skeleton ledger](PITCH_SKELETON_LEDGER.md), `m=k+1`, `n=3k+1`.
In a row with no H junction, horizontal midpoints are unmarked. Without
a pitch row, some junction in that row is vacant. No horizontal hit
can arrive at it. Transpose for columns with no V. These rows and
columns cannot intersect, so they give `2m-r-c` distinct zero-hit
vacancies. The second slack `v+doubles-hits` is exactly the number
of zero-hit vacancies.

Let `X` sum the slacks after subtracting this mandatory debit. The
skeleton forest has exactly `C` junction classes: a blank off-skeleton
site touches at most one marked midpoint (the two possible midpoints
are diagonal), so all junction paths follow realized coarse edges.
Every nontrivial skeleton component contains a junction. Write `A`
for the number of full-forest junction classes and `j=C-A`. Keeping
isolated junctions gives an unrestricted identity on the no-pitch class:

```
M = n*m + F - j - A - X,    X ≥ 0.
```

At 103 this forces **`F-j≥43`** for a 3647 forest. At every side an
above-comb no-pitch forest needs `F-j≥k+floor((3k-13)/10)+A`.
At `F=43`, `A=C=1`, `j=X=0`.

**Spacing at the floor.** Orient so just `b=min(r,c)` junction rows
contain H. In a row which, together with both existing neighboring
rows, consists entirely of V, consider each inward row of stubs.
If all its pitch sites are marked, some extra mark must occur between
two (no pitch). This forces a new middle bond between vertices
already attached to coarse junctions. Different physical rows supply
independent joins, charging `j`.

Otherwise each inward stub row has a missing slot. If its owner is
marked, the opposite slot is predicted too. Either that slot is
present and the edge survives, or two slots are missing on a single
failed edge. At most `2*slack1` rows can use this explanation. If
the missing slots are all owned by vacancies, two distinct vacancies
on the row cost an extra zero-hit vacancy; a sole vacancy with all
its inward stubs absent gives a completely isolated junction. None
of these cases is possible at `F=43`. Hence `3b≥35` at this floor.

**Cut transfer.** Cut and repair the skeleton alone by the
[single-cross rule](SINGLE_CROSS_MINOR.md), paying `L`. Set aside
the `near` off-skeleton marks at distance less than three from
either deleted line. The other marks and their incident edges keep
their geometry. Let `K` be the edges added by these distant marks
beyond the skeleton, and use as ports those vertices of `K` in old
junction components. All nonports have no base edges, before or
after the cut: they were isolated and the only added base edges lie
on the seam. Also the base edges forced by distant marks are unchanged:
the only base marks erased in repair lie on the seam.

Each tree component of `K` with `t` ports has capacity `(t-1)_+`
for independent joins. Contract the base classes. Each unit of
capacity either joins two classes or closes a cycle. Before cutting,
the joint port rank `j0` attains total capacity because the input
is acyclic. After cutting, let `j1` be the drop in the number of
port classes when the same trees are added to the new base. The
exact cycle rank is **`j0-j1`**. The union is diagonal-free, so
deleting a marked turn with a blank neighbor on a cycle pays at most
one mark per cycle. Thus before refill the loss is at most
`L+near+j0-j1`. In particular `j0≤j`; at `F=43` no distant join can
incur a repair charge, though `L` and `near` still need to be priced.

`python3 -B -m analysis.research_program.skeleton_cross_rank` replays
the component partitions and both resulting trees. On the 3610-mark
mixed control (`F=141,j=80`), cross `(2,2)` costs `35+102+14-14`
before 71 refills, net 66. The shifted-shell cross `(37,49)` loses
two joins (`587→585`); two cycle repairs and 55 refills give loss 75.
