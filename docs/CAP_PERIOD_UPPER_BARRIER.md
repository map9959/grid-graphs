# Residue one, `k=16+10j`: a barrier to repeating square-patch upper certificates

The period-ten construction has score `C(j)=851+1013j+300j²` on
`n=49+30j`, `j>=0`. To establish equality by a real upper estimate
and integrality we need an upper strictly below `C(j)+1`.

**Result.** The unrestricted 3-by-3 patch / oriented-star relaxation
has a feasible fractional solution of score

    C(j) + (4+3j)/9

for every such side. Consequently even the **unpooled** relaxation
cannot prove equality by rounding anywhere on this progression from
side 109 onward. In particular no choice of period-30 multipliers on
these same physical rows suffices. This is not a forest and does not
refute sharpness of `C` for integer spanning trees.

## Certificate searches

* Period 30 in each coordinate, two boundary correction layers, with
  normalization depths 6/5 for sites/patches: 31569 columns.
  The rational dual obtained at side 79 had excess coefficients over
  `C` of `190355847/25000000`, `1400007163/200000000`,
  `4699/400000000` in ascending powers of `j`. It misses the target.
  The base matrix and objective agree exactly at 49 and 79; coordinate
  types and each local incidence remain the same when adding 30.
  Multiplicities of an interior phase increase by one per axis per step;
  the polynomial RHS follows by multiplying the axis counts.
* Period three with five boundary layers instead gives, for *all* residue-one
  sides `n>=25`, the solver-free upper `n²/3+4n/3−5806/897`. On the test
  progression this is `C(j)+2450/299+7j`. It improves the previous
  integer bound `3k²+6k−4` by one, to `3k²+6k−5`, but still does not match.
  This uses the same fine-type charge argument as the other period-three
  duals, with agreement depth 5 and normalization depths 9/8.

## Why the obstruction applies without pooling

Use the saved 355 nonzero probabilities, assigning a site's or patch's
distribution according to its boundary distances and bulk phases, with
D4 symmetry. Use depth 8 on an axis of `n` sites and depth 7 on the
axis of `n−2` patch origins. Tying probabilities is permissible here
because the assertion is *existence of a feasible primal*. Agreement
equations are imposed **pointwise**, not merely on sums of like types.

All 5598 representative constraints are verified with rational arithmetic
on the template of side 28. To see completeness, local incidences reference
offsets at most two, and referenced axis lengths differ by at most two.
For an anchor within ten positions of an end, preserve its exact distance
to that end; all boundary tests and phases are then unchanged. Else use
an interior representative with the same residue and distance at least ten
from either end (available on both template axis lengths 28 and 26).
All referenced coordinates are then outside the explicit near/far layers;
the same is true in the reflected images, with the far distance of a
patch origin differing by at most two from the corresponding site distance.
Modulo-three reflection is unchanged because the larger side is congruent
to 28. Apply this separately on the two axes. Thus all the physical
normalizations, corner inequalities and overlap marginals are satisfied.

Boundary axis types have one site; bulk multiplicities increase by ten
per 30-column increment. Summing the selected-site probabilities against
the products of these two affine counts yields the exact quadratic above.
For an additional direct check, the independent replay expands the witness
to all 202973 unpooled rows at side 109 and obtains `36703/9` versus a
constructed score of 4077. Since `36703/9 > 4078`, no dual of these
rows can exclude score 4078.

```
python3 -B -m analysis.research_program.period30_cap_upper --replay
python3 -B -m analysis.research_program.repeating_patch_dual 5 --three --residue 1 --replay
python3 -B -m analysis.research_program.tied_cap_primal --replay
python3 -B -m analysis.research_program.tied_cap_primal --physical 109
```

The next certificate needs constraints outside this patch LP. A concrete
test is to separate the saved fractional marginals with strip-connectivity
states that remember whether two sites already belong to the same component,
as the four-row cap transfer does for its two terminals. Such cuts must be
necessary for arbitrary forests, not assume the cap construction.

## Four-row strip separation

The saved point cannot lift even on the single full-width strip of rows
6 through 9 (zero based). Write `p(j,r,m)` for the marginal probability
of 3-square mask `m` at `(6+r,j)`, where `r=0,1`. Masks use row-major
bits starting at the upper-left low bit. Let `S(j,r)` be the positive
support of the saved marginals. The following **unconditional** forest
inequality was found:

```
sum_{j,r} Pr(mask at (6+r,j) is outside S(j,r))
  + p(1,0,258) + p(1,0,288) + p(1,1,132)
  + p(n-4,0,66) + p(n-3,0,292) >= 1.
```

The first sum is essential: forests need not have the saved support.
For the saved primal that sum vanishes and the five remaining terms
sum to `67/72`. To verify validity, try to avoid every event in the
sum. Scan one four-bit column at a time; keep the last two bit columns
and the connectivity partition of the newest column, including paths
through the entire prefix. Add each newly forced horizontal or vertical
edge, rejecting a cycle. Discard transitions whose two newly completed
masks hit a charged event. No state survives to the far end. Thus every
forest must pay at least one, also after taking expectations.

The inequality repeats on all residue-one sides `n>=25`. Each end has
seven explicit patch layers; the middle support depends only on column
modulo three. On side 25, after physical columns 11 and 14 the sets of
surviving states coincide exactly (two states). Repeating those three
columns any number of times preserves that set, and the same remaining
suffix eliminates it. This proves validity at all larger sizes, not
just the tested 109.

In the depth-five pooled dual model (fine patch depth eight), sum the
cost once per fine position type, since its variable is already the
sum over the positions of that type. Rows 6 and 7 are singleton row
types, and each event coefficient depends only on the fine column
type. The resulting additional inequality has constant RHS one. Its
coefficient vector agrees at 25, 28 and 109. At 109 the old rational
dual remains feasible, and a *different* saved rational pooled primal
matches its value `1225659/299` while satisfying the new row. Thus the
new inequality separates the old physical witness but does not improve
that model's side-109 upper bound. This does not establish optimality
for the strengthened unpooled model.

```
python3 -B -m analysis.research_program.repeating_four_cover --replay
```

## The replacement pooled optimum fails already on one shared bit

At side 109, use the top four rows, with coordinates starting at zero.
The patches at `(0,5)` and `(0,6)` must report the same probability that
site `(2,6)` is selected. In row-major mask encoding, if `p_j(m)` is
the law at `(0,j)`, a separating inequality is

```
sum_{m: bit 7 set} p_5(m) <= sum_{m: bit 6 set} p_6(m).
```

In fact equality is necessary for any distribution on the strip, even
without acyclicity. Both patch origins are singleton fine position types:
depth eight records their physical coordinates without bulk pooling.
Thus the two reports are fixed by the pooled solution, regardless of how
its other masses might be distributed over physical sites.

Exact replay gives `15/46 <= 0` for the saved `1225659/299` optimizer.
Adding the equality to the depth-five model (in addition to the previous
event cover) rejects this optimizer. The row has zero RHS and the same
coefficients throughout the progression: both near distances are fixed
and their reflected positions have fixed far distances. A new rational
primal at 109 gives `15/46` on both sides and matches the unchanged dual
at `1225659/299`. This tests the single projected equality, not the full
four-row-strip model.

```
python3 -B -m analysis.research_program.repeating_four_cover --replay
python3 -B -m analysis.research_program.repeating_four_cover --replay --pinned
```

## Enforcing all single-site agreements on pinned neighboring patches

For depth-five pooling the patches have fine depth eight. At side 109
the individually recorded patch origins form four 8-by-8 corner blocks.
Each has 112 horizontal/vertical neighbor pairs, six shared sites per
pair. For each site require equality of the sum of probabilities of
masks marking it, as reported from each patch. The zero-bit equality
follows by normalization. Square symmetry and removal of duplicate
rows up to sign leave 336 distinct nonzero equations. The previous
single-equality optimizer violates 105, with maximum absolute discrepancy
`12/13`. This does not impose the full six-bit joint overlap law.

Adding all these equations to the prior depth-five model including its
four-row cover drops the exact side-109 LP optimum from `1225659/299`
to `3793203583/925484`. The independently replayed primal and dual
agree. The integer upper drops from 4099 to 4098; the cap gives 4077.

These rows have fixed zero RHS and constant coefficients on the
`n=25+3h` progression: near/far pinned coordinates have fixed end
distances, including after reflection, and the four pinned blocks
remain separated. The dual gives Newton coefficients
`217133407/925484,57,6` in `h`, i.e. the real bound
`3k²+6k−4982753/925484` for `n=3k+1>=25`. Its integer consequence is
`P(3k+1,3k+1) <= 3k²+6k−6`. Sharpness of the strengthened LP is
verified only at side 109, not asserted throughout the progression.

```
python3 -B -m analysis.research_program.all_pinned_sites --replay
```

## Full six-bit pinned overlaps

For each of the same 448 neighbor pairs, order the six physical shared
cells row-major in both patches. For each of the 64 words equate the two
sums of mask probabilities projecting to that word. These joint equations
imply the single-site equations by summation. Among the 28672 comparisons
there are 1344 distinct nonzero equations up to symmetry/sign; 267 fail
on the saved single-bit optimizer. All have zero RHS and the same
coefficients on the repeating progression by the singleton-position
argument above.

The strengthened depth-five model at 109 has matching exact primal and
dual score `1118890/273 = 4098 + 136/273`. This improves the real upper
by `4255057/36093876` but leaves `4077 <= P(109,109) <= 4098`.
The repeating dual's Newton coefficients are `64018/273,57,6` in
`h=(n−25)/3`. Its integer bound is unchanged throughout that progression.

```
python3 -B -m analysis.research_program.all_pinned_sites --joint --replay
```

## Redistribution cannot lift the saved six-bit optimizer

On side 109 consider the full-width strip on rows 5–8 (zero based).
For each `j=8,11,...,98`, the patches with origins `(5,j)` and `(6,j)`
share the six cells in rows 6–7, columns `j..j+2`. Let `E_j` mean
those six cells are all zero. Every strip law must satisfy

```
sum_j Pr_top(E_j) <= sum_j Pr_bottom(E_j)
```

(indeed equality). These are sums over the **entire** fine column type
8, with both row positions recorded individually. Any disaggregation
can change each individual probability, but cannot change the displayed
sums. The saved `1118890/273` optimizer gives `1/42` and `0`, so even a
distribution on arbitrary four-row bit strings cannot lift it.

For the repeating model, impose this equality for all 64 words, all
three bulk column phases, and vertical patch pairs at near row origins
`i,i+1` for `0<=i<=6` (with symmetry images implicit). Each fine-type
variable already sums over the phase, so no multiplicity factor is
applied. The coefficients are independent of side throughout the
progression and the RHS is zero. Of 280 distinct nonzero equations, 21
fail on the old witness. Nevertheless a different exact pooled primal
attains `1118890/273` and a matching dual certifies optimality after all
280 equations are included. The side-109 integer interval stays
`4077..4098`. This does not certify a full-strip lift of the new primal.

```
python3 -B -m analysis.research_program.redistributed_strip --replay
```

## A connectivity-dependent cut after phase-sum agreement

The replacement in `redistributed_strip_109.json` cannot lift on rows
0–3, even with arbitrary redistribution. For a 3-square patch in this
strip let `(c,r,m)` designate its fine column type, row origin (`0` or
`1`), and mask in row-major low-bit-first order. Write `P(c,r,m)` for
the **sum** of probabilities over all column origins of type `c`, and
`S` for the set of triples with positive saved mass. Column types are
0–7 at the near edge, 8–10 for the three bulk phases, and 11–18 at the
far edge. Let `E` consist of the following `(c,m)` pairs, all at `r=1`:

```
(1,256) (3,32) (3,384) (4,384) (14,16) (14,192) (15,192) (16,192)
```

Every four-row forest satisfies

```
sum_{(c,r,m) outside S} P(c,r,m) + sum_{(c,m) in E} P(c,1,m) >= 1.
```

Indeed, a physical outcome avoiding every charged event has **no**
surviving terminal connectivity state in the transfer that adds forced
edges and rejects cycles. When cycle rejection is disabled, three
terminal states survive at 109. Thus this certificate uses actual forest
connectivity, rather than only consistency of labels. It does not require
any individual column to have the average probability of its phase.
For the saved point the complement sum is zero and the total is `19/42`.

The support template and boundary events are fixed by type. In the
width-25 check the reachable frontier after column 12 equals that after
column 15, including the partition and both retained bit columns.
The transitions in between use three interior phases. Repeating them
adds three columns without changing the frontier; the unchanged suffix
eliminates it. Hence the cut holds throughout the repeating progression.
The saved support defines the coefficients, not an assumption on trees.

The added row excludes the old point by `23/42`. Exact primal/dual
replay at side 109 gives `1118890/273` again, with the cut tight (`1`)
on the new primal. The integer bound therefore remains 4098.

```
python3 -B -m analysis.research_program.redistributed_transfer --replay
```

## Complete top-strip transfer at 109

The exact optimum after adding the complete top-strip model is
`12293/3 = 4097 + 2/3`. It decreases the previous relaxed optimum by
`227/273` and yields the unrestricted integer upper **4097**.

The added variables are a nonnegative unit flow through 109 successive
four-bit columns. The state stores the last two column words and the
connectivity partition of the newest column through the whole prefix.
On inserting a column, add its forced vertical edges and all newly
forced horizontal edges crossing from the old column. A union within
an already connected component rejects the transition. Forgotten sites
cannot receive any later edges. Thus a path through this layered graph
describes exactly a four-row forest pattern, and flow decomposition gives
a distribution over those paths. The initial dummy column is unmarked
with four distinct components: its incident horizontal edges at the
first transition are pendant leaves and impose no constraint.

The graph has 51,629 legal arcs and 8,447 source/conservation equations.
For each of the two patch rows, 19 column types and 100 legal masks, a
link equates expected **total** occurrences on the path to the matching
pooled variable. No occurrence is prescribed separately inside a bulk
phase. No arc is suppressed on the basis of a previous primal's support.
An actual forest, averaged over the square symmetries and restricted to
rows 0–3, supplies such a flow, so the strengthening is valid for an
arbitrary spanning tree.

```
python3 -B -m analysis.research_program.full_top_transfer
```

This regenerates the model and checks the stored nonnegative primal,
every constraint, all dual column inequalities and equality of the two
rational objective values without an LP solver. It proves a bound at
side 109, not for the entire period-ten progression. The primal is still
a relaxation of a whole-square forest. With the 4077-site construction
the remaining interval is `4077..4097`.

## Complete joint five-row transfer at 109

The same pooled core point extends to a **single distribution on forests
of rows 0 through 4**. This is stronger than separate distributions on
two overlapping four-row strips. There are 230584 legal arcs, 25185
flow balances, and 5700 phase-total links (three patch rows). No interior
position is required to take its phase's average probability.

To find the lift, fix the four-strip optimum's pooled core and delete arcs
emitting masks whose total must be zero. The resulting flow is sparse.
Replay restores **all** arcs, assigns the omitted ones zero in the primal,
and checks every row in rational arithmetic. For the dual, retain the
old pooled and first-two-patch-row prices, set the new patch-row prices
to zero, and compute flow-balance multipliers by backwards dynamic
programming on the **unrestricted** five-row transfer. At each state the
multiplier is the maximum successor multiplier minus the arc price,
with terminal multiplier zero. This gives valid dual inequalities for
every arc, including those absent from the primal search. The exact
primal and dual both give `12293/3`; the fifth row does not lower the
integer upper. The new certificate only stores nonzero arc flows and
reuses `full_top_109.json` for the pooled variables and dual prices.

```
python3 -B -m analysis.research_program.top5_lift
```

## Top six rows: the saved optimizer cannot extend

Let `P(k)` be the total mass of the physical 3-square mask event
`k=(column type, row origin, mask)` across that column type, using the
four patch rows 0..3. Let `S` be the positive support of the saved core
in `full_top_109.json`. Put `e=(11,3,7)`: type 11 is just column 99,
and mask 7 selects the top row of the patch and no other sites.
A valid event-count inequality is

```
P(e) + sum_{k outside S} P(k) >= 1.
```

Min-cost transfer on the full strip shows that any supported forest
path must hit `e`; otherwise an unsupported occurrence costs at least
one. The saved point gives exactly `1/2`. Since the terms are complete
phase totals, redistribution among like positions cannot remedy it.
This excludes even a lift of the pooled core alone, regardless of which
five-row arc distribution is chosen.

The contradiction localizes to physical columns 97..101: when masks at
patch origins 97,98,99 (rows 0..3) stay in support, it is impossible
to avoid `e` even with cycle rejection disabled. Thus one can also sum
unsupported events just over the three corresponding column types.
Charging whole types, rather than only positions 97 and 98 in bulk,
keeps the localized inequality valid on the pooled variables.

With the first cut added to the five-row model, another exact flow and
pooled core score `12293/3` with cover value `13/12`. The previous dual
is unchanged, hence this is the exact new optimum. With the stronger
localized cut there is a verified feasible flow of score `233549/57`
(strictly above 4097), and the previous upper is still `12293/3`. Both
floor to 4097; no exact real optimum is claimed for the localized cut.
The full six-row relaxation was not optimized in this experiment.

## Complete six-row transfer: the integer upper stays at 4097

Let `V6` be the maximum after imposing a single distribution on forests
of rows 0 through 5 with all four rows of patch marginals linked. Exact
certificates give `4097 <= V6 <= 12293/3`, hence `floor(V6)=4097`.
This lower inequality is about the fractional LP, not the grid optimum.

For a primal certificate, a new pooled point has a unit flow with only
272 positive arcs. `top6_sparse.replay` checks all positive transitions
for acyclicity, conservation at every touched state, and all 7,600
patch totals, including zeros. All omitted flows are zero. Thus it
is feasible in the **complete** joint six-row model, regardless of
the support restriction used to discover it.

For the dual, retain the verified four-row prices on the first two
patch rows and give the other two rows price zero. The upper verifier
checks the core column inequalities and computes the minimum total
price of a six-row path by integer dynamic programming over **all
1,059,955 legal arcs**. Subtracting this minimum from the core dual
RHS gives the bound above. This certifies the optimal *integer floor*;
the two rational objectives are not equal, so this replay does not
determine the exact real-valued LP optimum.

```
python3 -B -m analysis.research_program.six_joint_replay
```

## Seven rows exclude 4097 even after redistribution

At side 109 let `V7` impose one full-width forest distribution on the
top seven rows. All five overlapping patch rows are linked to the core
by phase totals. The saved six-row point requires mass `1/8` at event
`(column phase 1, patch row 2, mask 288)`. No complete seven-row
path emits this event using only the point's positive labels.

Even if all pooled variables change, the certificates give

```
20483/5 <= V7 <= 1638722183861/400000000 < 4097.
```

The primal in `seven_lower_109.json` has 310 positive arcs; omitted
arcs are zero. Replay checks the pooled constraints, every transition,
conservation and all 9500 linked totals. For the dual, `seven_upper_109.json`
stores core multipliers and integer event prices in units of `10^-8`.
Replay checks multiplier signs and core reduced costs rationally, then
subtracts the minimum path price from the core dual objective. Its
integer dynamic program prices all 4953204 legal arcs and checks the
accumulator range. The sparse discovery model is not needed for replay.

```
python3 -B -m analysis.research_program.seven_threshold --fixed
python3 -B -m analysis.research_program.seven_threshold --replay
PYTHONPATH=target/lp-python python3 -B -m analysis.research_program.seven_upper
```

Thus `floor(V7)=4096`, and the whole-grid interval is `4077 <= P(109,109) <= 4096`.
The fractional primal is not a whole-grid construction.

## Eight rows retain the integer upper of 4096

The saved seven-row core at `20483/5` cannot lift: the event
`(column phase 3, patch row 1, mask 192)` needs mass `1/25`, but no
full-width eight-row path using only its positive labels emits it.
Forward reachability followed by backward pruning leaves 428 supported
arcs; the event is absent on all of them.

With redistribution, `eight_lower_109.json` gives one joint eight-row
flow scoring `12289/3`. Solver-free replay checks all core rows, 496
positive arcs, conservation and all 11400 phase totals from the six
overlapping patch rows. Other arcs have zero flow. Deleting the eighth
row of each forest preserves acyclicity and the seven-row links, so
the seven-row upper remains valid. Consequently
`12289/3 <= V8 <= 1638722183861/400000000` and `floor(V8)=4096`.

```
python3 -B -m analysis.research_program.seven_threshold --eight --fixed
python3 -B -m analysis.research_program.seven_threshold --eight --replay
```

## Nine rows exclude 4096

For the saved eight-row core of score `12289/3`, the event `(column
phase 1, patch row 2, mask 288)` requires mass `3/16`. Forward
reachability and backward pruning leave 402 supported arcs but no
full-width nine-row path emitting this event. Thus the fixed point
cannot lift.

Allowing the core to redistribute, the exact certificates bracket the
complete nine-row relaxation:

```
12287/3 <= V9 <= 1638358793533/400000000 = 4095.8969838325.
```

The lower replay checks 483 positive arcs and 13300 phase totals from
all seven patch rows. The upper replay checks the core dual inequalities
and prices every legal path using integer dynamic programming. The state
records the two most recent column masks and the connectivity partition
of the last column. Extending a path unions all newly forced edges and
rejects a transition if it closes a cycle. The Rust verifier generates
the reachable states from scratch and evaluates 111626206 reachable
arc occurrences over the 109 layers. Only the search for multipliers
used screened arcs; the certificate replay uses the complete graph.

```
python3 -B -m analysis.research_program.seven_threshold --nine --fixed
python3 -B -m analysis.research_program.seven_threshold --nine --replay
rustc -O analysis/research_program/nine_price.rs -o target/nine_price
python3 -B -m analysis.research_program.nine_dual
```

Consequently `floor(V9)=4095` and `4077 <= P(109,109) <= 4095`.

## Ten rows retain the integer upper of 4095

With the saved nine-row pooled point fixed, 541 arcs remain on supported
full-width ten-row paths. None emits `(column phase 1, patch row 3,
mask 6)`, although the point assigns that event mass `1/3`. Thus this
point has no ten-row lift.

With redistribution, `ten_lower_109.json` certifies a joint ten-row
flow scoring `28667/7 = 4095 + 2/7`. Replay checks the core constraints,
the 697 positive arcs and their conservation, and 15200 phase totals
from the eight overlapping patch rows. Omitted arcs carry zero mass.
Deleting the tenth row preserves the forest property and all nine-row
links, so the nine-row dual still applies. Hence `floor(V10)=4095`;
the whole-grid interval remains `4077 <= P(109,109) <= 4095`.

```
python3 -B -m analysis.research_program.seven_threshold --ten --fixed
python3 -B -m analysis.research_program.seven_threshold --ten --replay
```

## Eleven rows: the first vertical bulk patch

The patch starting at row 8 is the first one in a nonsingleton
vertical phase. Its core variable sums **31** rows; assigning that
total (or one thirty-first of it) to the strip row would not be a
necessary condition on a tree. Instead split patch coordinates 8
and 98 from the other 29 occurrences, on both axes to respect square
symmetry. The new patch variables are nonnegative sums over refined
coordinate pairs. For each old phase pair and mask, their sum, with
the multiplicities from symmetry, equals the old variable. Each of
the nine physical patch rows links to 21 column-phase totals; the
interior column probabilities can still redistribute. A physical tree
averaged over the square symmetries supplies such a joint distribution.

With the ten-row core fixed, 1079 arcs survive reachability and
full-width completion using positive labels. No such path emits the
required event `(column phase 7, patch row 7, mask 256)`, whose mass
would have to be `3/7`. Both coordinates here were already singleton
phases. With redistribution, `eleven_lower_109.json` independently
replays a score of `12283/3`; this lower bound is for the LP only.

The exact dual in `eleven_upper_109.json` checks every core column and
prices 2,609,959,367 legal arc occurrences on the full physical strip.
It gives `V11 <= 1310369986333/320000000 = 4094.906207290625`.
The primal replay checks 695 positive arcs and 18900 linked totals;
thus `floor(V11)=4094`. The whole-grid interval is now
`4077 <= P(109,109) <= 4094`.

```
python3 -B -m analysis.research_program.seven_threshold --eleven --fixed
python3 -B -m analysis.research_program.seven_threshold --eleven --replay
rustc -O --cfg eleven analysis/research_program/nine_price.rs -o target/eleven_price
python3 -B -m analysis.research_program.nine_dual --eleven
```

## Twelve rows preserve the score, but not the eleven-row point

Refine the eleven-row buckets by separating patch coordinate 9 and
its reflection 97 on both axes. Their refined totals sum to the
previous totals; no per-column probabilities are tied. With the saved
eleven-row point fixed, only 1860 arcs survive full-width reachability.
No supported path emits `(column phase 6, patch row 6, mask 7)`, which
requires mass `1/24`. Thus the point does not lift even if its strip
flow is allowed to change.

After redistribution, `twelve_lower_109.json` replays to **the same
score `12283/3`**. Its 541 positive arcs are one unit flow through the
entire width; all 23000 totals (23 column phases × 10 patch rows × 100
masks) and all pooled constraints are checked exactly. Deleting the
twelfth row and summing the refined buckets recovers an eleven-row
feasible point, so the previous upper applies. Hence `floor(V12)=4094`;
the whole-grid interval remains `4077 <= P(109,109) <= 4094`.

```
python3 -B -m analysis.research_program.seven_threshold --twelve --fixed
python3 -B -m analysis.research_program.seven_threshold --twelve --replay
```

## Thirteen rows: the fixed support dies inside the left boundary

Split coordinates 10 and 96 (reflections on the 107 patch positions)
from their previous pooled types on both axes. The new sums aggregate
back to the twelve-row variables. On the saved twelve-row point of
score `12283/3`, every extension has zero mass outside children of
positive parent types. Exhaustive forward reachability on this support
is empty at column 12 (zero-based): even the first thirteen columns
cannot be completed without an unsupported patch or a forced cycle.
Allowing the masses to change instead gives a rational primal of
`53205/13`, checked on 27500 patch totals.

For upper pricing one can represent the path price as two sums on
rows 0–8 and 4–12 respectively. The two projected words must agree
on their five common rows; a price added to a common three-column
pattern in the first word can be subtracted in the second without
changing any full path cost. Backward dynamic programming on each
projection gives lower bounds on the remaining cost. A forward budget
search joins compatible next columns, tracks both projected states
and the full thirteen-site connectivity partition, and rejects cycles
in the full graph. It discards a prefix only if its cost plus the
two suffix bounds exceeds the budget (or a cheaper prefix has the
same state). If no final state remains, every path costs at least
the integer budget plus one. The checker's resource-limit fallback
uses the valid independent suffix bound, never an exclusion from a
truncated search.

Exact replay of `thirteen_upper_109.json` gives `V13 <=
409397871693/100000000 = 4093.97871693`, with 1392498 retained arc
visits (not the size of the complete graph). Thus `4094` is excluded
even after redistribution, and `4077 <= P(109,109) <= 4093`. The
fractional lower `53205/13` does not settle the real LP optimum or
give a spanning tree.

```
python3 -B -m analysis.research_program.seven_threshold --thirteen --fixed
rustc --edition=2021 -O analysis/research_program/thirteen_price.rs -o target/thirteen_price
python3 -B -m analysis.research_program.thirteen_replay
```

## Fourteen rows: fixed-point test and pricing

Split patch coordinates 11 and 95 from the previous buckets on both
axes, preserving the sums for each old bucket and mask. The strip
links all twelve patch rows over the 109 physical columns to 27
column phases. With the saved thirteen-row core fixed, only 274 arcs
lie on a supported full-width path. None emits `(column phase 3,
patch row 1, mask 328)`, whose required mass is `1/8`. With the
core free to redistribute, the saved joint flow scores `12275/3`.

For pricing, two nine-row projections start at rows 0 and 5. Each
pair of next columns must agree on all four common sites. The joined
state retains the fourteen-site connectivity partition and rejects
any edge closing a forced cycle. The negative of any message price
used on a shared pattern in the first projection is used in the
second, so these messages do not change a joined path's price.
Suffix price bounds permit budget pruning. If a large layer is
trimmed, the verifier records the smallest discarded sum of regrets:
each future regret is nonnegative, so that sum remains a lower bound
for every discarded continuation. Beam paths are for discovery only.

`fourteen_upper_109.json` replays to the exact upper
`327438177487/80000000 = 4092.9772185875`, strictly below 4093.
The separate primal replay checks 558 positive arcs and 32400 phase
totals. Its score `12275/3` concerns the relaxation, not a spanning
tree. The resulting whole-grid interval is `4077 <= P(109,109) <= 4092`.

```
python3 -B -m analysis.research_program.seven_threshold --fourteen --fixed
python3 -B -m analysis.research_program.seven_threshold --fourteen --replay
rustc --edition=2021 --cfg fourteen -O analysis/research_program/thirteen_price.rs -o target/fourteen_price
python3 -B -m analysis.research_program.fourteen_bound
```

## Fifteen rows exclude 4092

The joint distribution spans all 109 columns. Both axes split patch
coordinates 12 and 94 out of their old buckets; the finer probabilities
sum to the old masses and are free to redistribute. The rational feasible
flow scores `12274/3 = 4091 + 1/3` (437 positive arcs; 37,700 phase totals).
The dual gives `409199996933819001/100000000000000 < 4092`. Thus the
**floor of the fifteen-row optimum is exactly 4091**, and the whole-grid
interval is `4077 <= P(109,109) <= 4091`.

For this dual, integer path pricing needs only three nine-row projections,
at offsets 0, 3 and 6. The outer two carry the original prices, the middle
one starts at zero. At every column, opposite messages price the same
three-column pattern on the six shared rows of each neighboring pair.
They cancel on every physical word. Summing the three separate minimum
costs gives a lower bound for the cost of *every* full-width fifteen-row
forest word, regardless of discovery support. This already clears the
budget, so the number of retained full-strip arc visits is zero.

```
rustc --edition=2021 --cfg fifteen -O analysis/research_program/thirteen_price.rs -o target/fifteen_price
python3 -B -m analysis.research_program.fourteen_bound --fifteen
python3 -B -m analysis.research_program.seven_threshold --fifteen --replay
```

## Uniform nine-row upper for residue one

For every `k >= 36` the unrestricted upper is **`3k²+6k−9`**.
This extends a strip bound to an infinite progression; it does not assume
that an optimizer, tree, or strip law at side 109 repeats. Keep the
nine-row patch prices, and modify the rational core multipliers by the
entries of `uniform_nine_repair.json`. The core matrix is constant and
its RHS has the Newton coefficients verified by `polynomial(5,3,1)`.
The additional corner agreements have zero RHS. The two event covers
have constant RHS one (for the last cover the reachable support set
repeats after three columns; see `redistributed_transfer.certificate`).

At width 109 let `F` be the entire vector of minimum costs immediately
before the eight far-end patch origins. The extra three bulk columns use
the same phase transition `T` at every later width. Integer replay on
22,412 states checks `T(F) >= F + 29777268/10^8` componentwise.
Min-plus updates are monotone and commute with scalar addition, hence
the price lower bound grows by at least this much per additional three
columns, even after the unchanged right-end updates. The width-109
price is `854657641/10^8`. The repaired core RHS has second difference
exactly six, and first Newton coefficient in `(n-25)/3` exactly
`57 + 29777268/10^8`. Subtracting the price bound gives the real upper
`3k²+6k−329631704767/40680000000` throughout `k>=36`. Rounding down
proves the claim.

```
rustc --edition=2021 --cfg uniform -O analysis/research_program/nine_price.rs -o target/nine_uniform
python3 -B -m analysis.research_program.uniform_nine
```

```
python3 -B -m analysis.research_program.six_cover_upper
python3 -B -m analysis.research_program.six_cover_upper --local
python3 -B -m analysis.research_program.top5_lift
```
