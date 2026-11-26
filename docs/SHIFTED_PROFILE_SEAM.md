# Opposite off-phase cuts cost linearly many defects

Let `n=3k+1≥94`. In the three rows centered at row 2 count all marks
outside column residue `p` modulo 3; call this `e`. Define `f`
similarly around row `n-7` in residue `q`. If `p≠q`, then **every**
marked forest satisfies

```
score ≤ 3k²+5k+floor((2k-15)/10) + e + f .
```

The constants improve for some ordered phase pairs. In particular a
forest reaching the comb needs `k/10+O(1)` errors between two such
incompatible cuts. Two exactly shifted cuts of the *same* nonzero
phase also cost at least one mark relative to the comb. The result
holds after reflection, rotation or exchanging the ends. It constrains
the full square, not a repeated filling.

**Terminal accounting.** First impose both profiles exactly. Each
cut row is a forest of `r=k+1` terminals. Phase zero has `r` rails;
phase 1 or 2 has `k` rails and one isolated, unmarked end vertex two
steps from the last rail. Keep this last vertex as a terminal. Every
rail has one compulsory normal contact to the seam, and its lateral
neighbors cannot have marked normal neighbors. The extra end terminal
has one optional normal contact (present iff the adjacent seam site is
marked). Let `C` count the seam classes of the `2r` terminals, counting
isolated terminals too. Orient every class with a contact toward one
of its terminal contacts. Thus `C` counts outward spokes at both ends
**plus** inactive end terminals. Let `c,d` be the separate cap class
counts. After gluing, the ranks of the three partitions cannot sum
above `2r-1`; otherwise their union contains a cycle. Hence
`C ≥ 2r+1-c-d`.

For seam height `H=n-10` and `M` seam marks the verified upper for
`10M+7C-10Hr-7r` is `-k-2` if exactly one phase is zero, `-k-5`
if both are nonzero and distinct, and `-6` for equal nonzero phases.
The rectangular star/patch LP has no reflection, no tied masks and
no wired-top assumption. Three rational duals at `(H,N)=(12,43)`
have these bilinear bounds throughout the step-three height/width
chart; the replay checks all column inequalities, normalization
counts and neighboring matrix signatures.

The two free caps maximize `10*marks+7*classes`. After subtracting
`10*depth*r+7r+3k`, the upper at depth two is `-10` in phase zero and
`-3` otherwise; at depth six it is `-10` and `-13`. Full frontier
vectors agree up to their shift after 30 more columns. Combining the
caps, seam, and actual numbers of marks in the two cut rows gives
`shifted_profile_bound.bound10(k,p,q)` in tenths. The displayed bound
uses the weakest mixed-phase constant.

For incomplete profiles delete the `e+f` off-phase marks, then insert
missing rail centers. The [cycle surgery for incomplete rails](UNBOUNDED_RAIL_SEAM.md)
works unchanged at shifted ends: adjacent free-row lateral sites have
no remaining normal mark, and distinct inserted centers have distance
at least three. Each insertion pays for its possible one-cycle repair
without removing prescribed marks. The isolated end terminal need
not be marked.

```
python3 -B -m analysis.research_program.shifted_profile_bound
```

## A changing phase within one cut

Take `z=30+3u`, `n-z=34+3v`, `u,v≥0`, `n≥94`. On row 2 use phase
zero through column `z`, then phase one from `z+4` to the right
edge. Use ordinary rails on row `n-7`. All masks between and beyond
these two rows are free. The upper in tenths is
`30k²+53k-10-b`, `b=(n-z-16)/3`. In particular this partial phase
change cannot beat the comb. With incomplete cuts add ten times the
number of off-profile marks in the two three-row neighborhoods,
by the same repair argument.

Here the upper cut contains `k` rails and two ghost terminals (inside
the 4-spacing and at the eastern edge), hence `k+2` classes before
gluing. The seam upper for `10M+7C` is `10Hr+7r+3-b`. Construct the
chart from `(H,n,z)=(12,31,15)` with three independent insertions:
vertical triples, triples west of the slip and triples east of it.
The fine labels clip the slip offset as well as both true end distances.
Each horizontal normalization count is affine in the two padding
counts (the added triples have the three middle residues on their
respective sides); multiply by the independent affine height count.
Replay checks all eight coefficients by evaluation and all neighboring
matrix signatures. This does not repeat any interior mask.

The slipped two-row cap has weighted upper `27r+3k+4`, by pumping
first the west, then the east three-column block; its terminal classes
include both ghosts. The ordinary six-row cap contributes `67r+3k-10`.
Combining these with `2r-1` prescribed marks and subtracting
`7(2r+2)` for the partition inequality gives the stated bound.

```
python3 -B -m analysis.research_program.one_slip_bound
```
