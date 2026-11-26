# Opening the nine-layer collar at one movable cut

Write `m=n-20`, and let `T` count the outer nine layers. The four
straight arms each have `m` columns of depths `0..9`. The last depth
is an unscored backing path. Suppose its holes on each arm are at
least three apart. Then, with **all straight cut words free**,

```
T ≤ 12m+151 = 12n-89.
```

Depth eight is free, even at the ends of the arms. This suffices for
the comb increment on passing to side `n-18`. In particular the
class cannot exceed `1147+2499=3646` at side 103. Split according
to whether a single straight slice has marks at depths `0,3,6` and
no others through depth eight. The first calculation uses that slice
wherever it occurs; the second handles its complete absence.

**Physical sweep.** Duplicate the chosen column and open the collar
there. The piece contains all the vertices of depths zero through nine.
Treat the four innermost corner bits as blank; these marks are not
counted and deleting them can only remove forced edges. Across every
inner corner, the two immediately adjacent depth-nine arm ends cannot
both be marked: those sites are diagonal in the original grid. The
sweep explicitly carries one bit through the bend for this test. It
matters: with depth eight free, omitting it changes the scalar price
from 451 to 452, which fails the final rounding.

Flag the three marked vertices on each copy of the cut. Merge actual
physical forest components on every edge forced by either endpoint.
When both components have seen a flag, increase `r` by one. Thus `r`
counts the identifications of the six terminals. In the original,
the three marked groups on one cut are disjoint before using the
rest of the collar. Contract common seam edges first. Restoring the
cut identifies three pairs, and a forest on three seam groups has
rank at most two. Hence `r≤2`. One can ignore the other seam groups
in this inequality: projected terminal identifications can only have
lower rank than with all the gluing constraints.

**The all-length computation.** The frontier stores the literal
mark bits, their partition (including isolates), a flag per live
class, and the truncated time since the last missing backing site.
The latter resets across a corner. In a straight section a column
transfer `F` adds three per scored mark, and each flagged merge
subtracts two. Starting at its input vector `d`, iterate
`d ← max(d,F(d)-9)` including absent states. Once there is no
improvement of any entry, induction bounds *every* length, including
zero. The sites left on the two ends of this update are the same
ordered list of ten depths. Three complete arms are required to have
length at least six; the two parts of the cut arm have arbitrary
lengths. Relaxing equality of these lengths is safe.

There are `4m-1` free columns. The score excluding both copies of
the cut is `T-3`. Four successive corner transfers give
`3(T-3)-9(4m-1)-2r ≤451`. Therefore `3T≤36m+455`, proving the cap.
With all depth-eight bits on the arms blank the scalar is at most
450 even with the inner diagonal relaxed.

**The no-pitch branch, including free depth eight.** In this branch an
arbitrary physical cut can be used. Duplicate the fourth slice from
the corner. Tag its `b` scored marked vertices and its backing vertex,
on both copies. If the seam edges alone join these `b+1` sites into
`g` groups, put `e=b+1-g`. In the opened forest the full flag rank
satisfies `r≤2e+g-1=b+e`. There are `2e` duplicated internal joins
and at most `g-1` independent joins of the common groups. Count
`6` per mark, subtract `4` for each flag join, and add `2e-b` on
each copy. Subtract `18` per free column to obtain a scalar `s`.
Then `6(T-12m)≤s-18`.

With the `036` slice forbidden throughout the four arms the relaxed
maximum was `s=930`. Thus any `T≥12m+152` must attain that exact
maximum. Propagate a 64-bit set of opening signatures along with
each best score, taking unions on ties (including ties in the
length closure). Filter both ends at depths `0,1,3,4,6,7`. The only
matching maximizer has depth zero marked and the other five blank
(`tags=0x2`; bit zero of the signature corresponds to depth zero).
By square rotation and reflection this restriction holds on the
fourth column from **either end of every arm** of such an input.
Imposing the decoded signature on the three uncut arms drops the
scalar to **926**, strictly less than 930. Thus the one-mark excess
was impossible. Both calculations used free depth eight and the
diagonal corner test. Each uncut arm has eight required columns,
with arbitrary additional length in the middle on the second pass.

**An unrestricted straight-arm inequality.** Allow all ten physical
bits including consecutive holes, with no end conditions. Let `h_j`
count successive pairs of backing holes at distance exactly `j` within
one arm of length `L`, and let `A` count marks in its first nine
depths. The three-column age and full forest partition give

```
A ≤ 3L+6 + min(h₁+h₂/6, (4h₁+2h₂)/5).
```

Both potentials are verified on 2,440,303 transitions, not inferred
from a sample of lengths. An arbitrary `10×10` corner excluding its
inner corner has free maximum 41. Thus summing these inequalities
gives an unconditional price on `T` (overhead `188` before charging
short gaps). This does not on its own pay the induction budget of
151. In particular, a distance-two pair and a missing perimeter
edge on the retained square are different defects.

The full four-corner transfer gives a substantially smaller constant.
Allow every bit on the ten layers, including arbitrary short gaps.
In the marked-terminal cut calculation charge six units when a hole
follows its predecessor immediately and two when it follows at
distance two. The scalar maximum is **954**. In the cut arm this
may omit a short pair straddling the cut, but never charges a pair
twice. There is no charge across a corner. Therefore, summing the
two gap counts over the four arms, for *every* square in the range,

```
T ≤ 12m+156+h₁+floor(h₂/3).
```

The calculation releases the entire straight and corner words, not
just the depth-nine bits. In particular, a physically attainable
rim gain on the smaller square of at least `5+h₁+floor(h₂/3)`
pays the comb increment in an induction step. For larger sides
this is not the same as paying the entire known unrestricted gap
in a single step.

**A core price that needs only the rim word.** In any `s`-square,
choose isolated marked teeth on each boundary side, spaced at least
three along that side. At a corner there is just one tangential
neighbor on that side; choose the physical corner at most once.
The four lists may have unrelated phases and arbitrary omissions.
Let `t` be the total chosen, `r,c` the core marked runs and forced
components, and `D` its marked degree deficiency. Then `r+c≥t`.
In particular `3I≤s²+D-t`.

Each tooth requires a normal marked run (a singleton is allowed).
If `j` pairs use the very same run, these are solid spanning rails.
They must lie on one axis: two perpendicular solid marked rails
would force a unit cycle. There are `t-j` distinguished runs.
In each open slab between consecutive distinguished solid rails,
there is no distinguished normal run on either of the first two
columns after its left rail: both ends of the rail were chosen and
each end list is spaced at least three. A transverse distinguished
run rooted on a lateral side cannot enter the slab past a solid
rail. Thus a slab without an extra run separates its two rails,
by the cut between those first two columns. Each extra run can help
in at most one slab since it cannot cross a solid marked rail.
Hence the extra runs together with `c` number at least `j`. This
proves the claim without knowing the interior partition. Long
marked runs on the two lateral sides that avoid the corners
cannot help in an open slab either. One may add the smaller of
the two opposite-side totals of such runs (count each length≥2
run once) even without knowing the direction of the solid rails.

On the ordinary 103 comb's `85×85` core the rim alone has
`D=228,t=58`, proving `I≤2465`. The old nine layers have 1181
marks, giving **3646** without assuming any particular wiring
behind that core word. At 133 the corresponding sum is
`1554+4485=6039`. These measured collar counts must not be
substituted for universal collar caps.

```
rustc -O analysis/research_program/dense_movable_cut.rs -o target/dense_movable_cut
target/dense_movable_cut 3 146 146 4 6 0 0 1
target/dense_movable_cut 3 255 255 4 8 1 1 1 3 1 0 1 0 1 3 4 6 7
DENSE_TAG_LOCK=1 target/dense_movable_cut 3 255 255 4 8 1 1 1 3 1 0 1
rustc --edition=2021 -O analysis/research_program/dense_defect_tariff.rs -o target/dense_defect_tariff
target/dense_defect_tariff 6 6 1 0 0
target/dense_defect_tariff 5 4 2 0 0
target/collar_bend elbow 9 1 1
DENSE_DEFECT_FEES=6,2 target/dense_movable_cut 3 255 255 4 8 1 0 1 3 1 0 1
python3 -B -m analysis.research_program.boundary_tooth_debit
```
