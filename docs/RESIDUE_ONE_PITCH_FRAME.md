# An actual pitch frame in an unrestricted square

Let `h` be the smaller of the numbers of bill-at-most-two blocks on
the two axes, using the disjoint blocks of
[the cheap separator lemma](RESIDUE_ONE_CHEAP_SEPARATORS.md).
Put `t=floor(h/24)`, `u=ceil(t/2)`, `v=ceil(u/2)`. If `v≥2`, there is
a rectangle (after possibly transposing the board) with all of the following:

* At least `v` distinct rows, including both ends, carry the **same
  complete pitch-three profile** between the vertical sides.
* At least `v` distinct columns, including the two sides, are **fully
  marked from end to end**. In particular the pairs of end teeth on
  those columns are connected by actual paths in the forest.
* Both dimensions are at least `3v-2`. In a board at least as good as
  the comb, `h≥1+floor((3k-13)/10)`; the resulting guarantee is linear
  in the side, not a fixed-window assertion.

**Choosing the rectangle.** Split `24t` cheap middle lines on each
axis into 24 successive groups of `t`. Expand each group's physical
span by one at both ends. Expanded spans on the same axis are
disjoint because the middle lines are three apart. Each cheap line
has at most four piece breaks and two billed events, so it is bad in
at most six transverse group spans. Here bad means a break internal
to the span or a charged site of the three-line block in the span.
For a pair of groups discard its bad lines on both axes. Averaged over
the `24²` pairs, at most `12t/24` lines in total are discarded.
Some pair therefore retains at least `u` lines on each axis.

At any retained crossing neither line changes type in its span.
Two empty lines would isolate the site; two full lines would force
diagonally adjacent marks. A full and an empty line disagree at the
site. Two pitch lines would give either a run start at the site or
two diagonal marks among its four neighbors. Thus exactly one axis
is pitch on every crossing. Since every retained line crosses every
retained perpendicular line, one entire family is pitch and the other
constant.

Call the pitch lines rows. Divide them into upper and lower halves,
including the median in both for an odd count. A retained full column
is already a rail in both halves. At an empty column `j`, marks at
`j+1` form a prefix down the span: a new mark there after an empty
site would have neither a west nor a north mark, and its start would
be charged in this column block. After that prefix the marks at `j-1`
must be continuous or a site of column `j` would be isolated. Thus
at least one half has an actual full rail at `j±1`. The argument
transposes, since the run-start test is symmetric in north and west.
In one common half at least `v` such parallel rails survive. They are
distinct (source columns are separated by at least three), and one
pin on a pitch row fixes its phase. Use the extreme pins and extreme
retained rows of this half as the frame.

## Exact tariff for the framed rectangle

More generally let a rectangle have width `3p-2` and height `H≥2`
and prescribe only its top and bottom words, with marks exactly in
columns `0,3,...,3p-3`. The maximum number of marks is **`Hp`**, for
arbitrary lateral sides. The `p` straight rails attain it.

To see the upper bound let `B` count pitch columns that are not
solid. Runs meeting an end row are vertical, allowing singletons.
There are `p+B` such runs: one per solid column, and separate top
and bottom runs on every broken column. Let `E` count the other
runs. Of the `p-B` solid rails, two consecutive ones cannot belong
to the same component if their intervening open strip has no `E` run.
Indeed, inside that strip all marks are on pitch columns; there is
an unforced edge between successive columns' stars on every row.
This separates the whole rectangle, even at its top and bottom.
An `E` run can occur in at most one intervening strip. Consequently
the component count `c` (including isolated sites) is at least
`p-B-E`. With `R=p+B+E` this gives `R+c≥2p`.

The rectangular edge ledger is `3M+R+b+c=HW+2H+2W` with missing
boundary incidences `b`, corners counted twice. The straight filling
has `R+c=2p` and minimizes `b` since both lateral sides are full.
Subtract the two ledgers. This also shows that missing lateral
incidences cost at least a third of a mark apiece relative to `Hp`.

The tariff bounds the marks in the crop. Substituting straight rails
in the full square can change exterior connectivity; only the
selected pins are known to connect their end teeth.

## Exterior price from the proved pins

For a strictly interior frame let `s` count known solid pitch columns
(including its sides). Delete the rectangle, leaving `A=n²-HW` sites.
Let `B` count marked outer boundary incidences, corners twice; `R` the
straight marked runs in this exterior; `t` the marked exterior sites
immediately above or below end teeth; and `z` the exterior components
having no forced edge to the rectangle. Then

```
3 M_out ≤ A + B - 2H - s - 1 - (R-t) - z,
3 M_total ≤ n² + B - s - 1 - (R-t) - z.
```

There are exactly `2H+2p` crossing edges: one per lateral site per
side and one per tooth per end. At other end sites a marked exterior
neighbor would be diagonal to a tooth. Every exterior neighbor of a
solid side is unmarked for the same reason. On the inside, the contacts
therefore lie in at most `2p-s` components: the two side bars already
lead to end teeth, and the `s` pins give disjoint identifications of
tooth pairs. Contract the inside and outside components separately.
The crossing multigraph is a forest, so at least `2H+s+1` **distinct
exterior components** must meet it. The edge ledger on the exterior
is `3M_out=A+B+t-R-c`, with `c` all exterior components. This proves
the first bound; the second uses `3Hp=HW+2H`. Each of the `t` sites
belongs to a distinct end run on its own side of the hole (its
lateral neighbors are unmarked), so `R-t≥0`.

`python3 -B -m analysis.research_program.frame_exterior` independently
counts the exterior contacts and their components. For the test frame
in the side-103 comb there are 33 pins, 248 crossing edges and 216
exterior classes, exactly the required minimum. The exterior bound
is 643, equal to the actual 643 marks. Its remaining debits `R-t,z`
were measured on that forest; bounding them and `B` for an unknown
maximizer is necessary before claiming the square upper is 3646.

The [exterior pin price](EXTERIOR_PIN_PRICE.md) now bounds that
functional from the frame geometry alone, excluding families of
off-phase placements at every exterior filling.

```
python3 -B -m analysis.research_program.cheap_cut_language
python3 -B -m analysis.research_program.cheap_cut_mesh
python3 -B -m analysis.research_program.pitch_rectangle_audit
```
