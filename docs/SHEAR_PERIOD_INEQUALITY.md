# A period-free ledger and a strict all-period bound for six-row pockets

Use the sheared-pocket geometry of `THREE_COLUMN_CROP_REPAIR.md`. Write
p for the number of triples in a repeat, H=hi-lo+1, S for the sum of
selected core and paired-frame sites, and G=S-pH for the net. The side
strip allowance requires G>=8p. No periodicity shorter than p is imposed.

## Exact ledger, arbitrary H and p

On the contracted quotient graph, count all vertices, including isolates.
Define:

* b = unselected sites among the 6p physical outer-boundary sites;
* R = S minus the number of selected-selected physical edges between
  variable sites, minus the number between a variable selected site and
  an immutable rod center. Include frame-to-rod FF edges. This is the
  *increment* of the Euler characteristic of the FF graph beyond the
  immutable rods, not the number of distinct contacted rod roots.
* t = V-E for the occupied quotient, with translations retained on the
  edges. On a feasible repeat each component is a tree or has a single
  nonzero-winding cycle, so t counts exactly the tree components.

Then, independent of H and p,

    3(8p-G) = b + R + t - p.                                  (1)

To count V: in one triple, contracting the fixed star support absorbs
two variable sites (the two tips adjacent to immutable centers). There
are three additional uncontracted U neighbors just outside the window
in column 2, which can be touched from the next block's column 0.
At the horizontal block seam the relative row changes by three.
Counting by physical columns gives the following
exact list of nonrod vertex rows adjacent to a free site (local coords):
column 0 has [lo,hi-1], column 1 has [lo+1,hi], and column 2
has [lo,hi+3].
Together these have 3H+1 sites. Add two rod roots and 18 frame sites:
`V=p(3H+21)`. Count E starting with the 2p forced frame contacts even
when no variable sites are selected. Summing physical degrees at selected
sites adds `4S-(6p-b)` and double-counts precisely the FF edges subtracted
in R (including contacts already forced by an immutable center). Thus
`E=2p+3S-6p+b+R`, giving (1). The identity also holds on cyclic inputs
if t is kept as V-E, rather than called a component count.

For one optimal witness of each independently verified period:

| p | G | b | R | t | b+R+t-p |
|--:|--:|--:|--:|--:|--:|
| 2 | 15 | 0 | 3 | 2 | 3 |
| 3 | 23 | 0 | 4 | 2 | 3 |

Strict `b+R+t>p` would imply `G<=8p-1` uniformly, by integrality.
Equation (1) alone does not show strictness. In particular a period-three
height-nine core **without frame centers** admits 28 centers from an
original 27. Separate claims of "no positive core gain" and "frame at
most 8p" therefore do not suffice.

## A strict local inequality for every period, with H=6

Free all three columns on local rows -1..4. For each pocket enumerate
every center mask. Preserve connectivity within its forced forest and
its connections to neighboring immutable rods. On the left and right
boundary separately keep the partition of the boundary sites, the
adjacent root, and the selected sites. In the adjacent-pair test glue
the right profile to the next left profile, adding an actual cross-edge
iff either endpoint is selected (fixed edges already contracted).
Reject repeated unions. Call the join split, s=1, when B_j is not
connected to A_(j+1) in this two-pocket test. Additional paths farther
away could remove a split; allowing it in the frame relaxation is safe.
The delta on each step is pocket centers minus H. Profiles from the
same pocket are selected as a pair, not optimized separately.

There is a verified potential on the left profile states such that for
every allowed `left -> right -> next left` transition,

    5*(2*delta+s) <= 4 + phi(next left)-phi(left).              (2)

This is computed by max-plus iteration. If the full vector of scores
repeats after q steps up to a constant a, form phi as the pointwise
maximum of the q successive vectors, scaled by q with a*i subtracted
at step i. The code checks the resulting edge inequalities explicitly;
no extrapolation of a scalar maximum. The left/right factorization is
relaxed only in forgetting connections through more distant blocks.
A second direct two-pocket physical-edge enumeration gives the same
maximum mean for this window.

Sum (2) around a repeat to get `2 sum(delta)+sum(s)<=4p/5`.
Independently the six-lane frame transfer in `modified_crop.py` has
`frame-sum(s)/2<=15p/2` on any repeat: its open vector gains exactly
7.5 per triple after its transient, so unrolling an arbitrary closed
repeat many times and dividing discards the endpoint constant. Summing
the bounds cancels the split term and yields

    G <= (79/10)*p, hence G <= 8p - ceil(p/10).

Unlike testing periods two and three, this excludes the target **for
every period**, including nonuniform sequences of pocket shapes, within
the six-row window. It gives 15 and 23 for p=2 and 3, consistent with
the attained values (the six-row period-three witness is also directly
replayable). It is not a height-independent theorem: at rows -2..4
the same relaxation only gives `2 sum(delta)+sum(s)<=p`, i.e. `G<=8p`.
One can still exclude equality at height seven as follows.

### Strictness at seven rows, any period

Write `N` for the total frame score and `s` for the split count. The
previous unit-penalty frame certificate gives `N-s<=7p`. Combining
this with `2 delta+s<=p` gives `G<=7.5p+s/2`. Since `s<=p`, attaining
8p requires `s=p`, zero total core gain and `N=8p`. In fact each side
has score <=4p, with a **unique** equality pattern regardless of p.
The single-side block automaton retains the last column mask and its
partition, uses a fresh rod root for each triple, and forgets that
root only after its third contact. A verified longest-path potential
on the nine reachable states bounds the score per triple by 4 plus a
telescoping difference. On its tight edges, the only word on a directed
cycle is `(4,5,4)`, up to the phase translation on the opposite side.
An infinite repetition attaining equality must follow tight cycles
after an initial transient (finite state, nonpositive cycle gain); its
periodic mask word is consequently this word throughout. In physical
terms the boundary row is full and each rod is attached to it by a
rung. Both frame components have winding. A core connecting two rods
of one side closes a physical cycle via its boundary rail; connecting
top to bottom merges two winding components, also forbidden.

Repeat the local profile test with all four rods in an adjacent pair
required to stay in distinct components. Even this relaxation forces
`2 sum(delta)<=-2p/5`. The potential was verified on 69,460 compatible
adjacent-profile joins. This contradicts the zero core gain needed at
equality. Thus **G<=8p-1 also at height seven**. At rows -2..5 (height
eight) the unit-price certificate gives `sum(delta)+sum(s)<=p` on
661,852 compatible joins. Adding `N-s<=7p` gives the non-strict
all-period bound `G<=8p`. The tight graph has a 428-vertex strongly
connected component; a tight local cycle does not certify a consistent
global core-and-frame configuration. The arbitrary-height version of
(1)'s strict inequality remains open.

    python3 -B -m analysis.research_program.shear_period_inequality
    python3 -B -m analysis.research_program.shear_packets -1 4
    python3 -B -m analysis.research_program.shear_packets -2 4
    python3 -B -m analysis.research_program.shear_frame_equality
    python3 -B -m analysis.research_program.shear_packets -2 4 --separate
    python3 -B -m analysis.research_program.shear_packets -2 5 --unit --critical
    python3 -B -m analysis.research_program.triple_pocket -1 4 3 23

## Eight rows: the physical equality product is empty

For the full window `-2..5`, equality in `G<=8p` requires equality in
**both** `sum(delta)+s<=p` and `N-s<=7p` with the same sequence of split
bits. On the core side keep all 494 physical masks that attain a tight
edge of the unique recurrent 428-vertex bipartite component. Recompute
the unit-penalty frame score vector after the transient. At the end of
three columns this vector shifts by seven on every state; thus equality
requires every step to be tight with respect to the corresponding
phase's potential. The recurrent part has 30 frame states and 266
labeled three-column transitions. A repeated physical configuration
could enter these critical graphs after a transient, since the finite
relaxed state follows a periodic word; no transient can compensate a
strict loss per repeat.

Synchronize the frame's split at the end of block j with the cut
between core blocks j and j+1. Restore each actual 24-site core mask
and all three six-bit frame masks. Construct the joint tile graph
on immutable rod star components and actual vertices; an internally
cyclic tile is rejected. Keep all core and frame identifications
together, including the next bottom rod contacted at the third column.
The incoming/outgoing interfaces each contain six frame sites, eleven
core separator sites (including U sites) and one retained rod. At a
join, add each physical horizontal edge whose left or right endpoint
is selected, and identify the common rod once. A repeated union means
a cycle, even if the original physical attachment edges were distinct.
Project the result onto the outgoing interface. The empty incoming
state has no selected sites or connectivity, which favors feasibility.

After deleting nonrecurrent arcs of the symbolic product there are
1,001 states and 19,678 labeled arcs (1,613 different physical tile
summaries). Exhaustive transfer starting at **every** such state gives

    consecutive tight blocks:  1     2    3    4    5   6
    reachable product states: 5681 3379  855  350  192   0

An infinite equality repetition would have a six-block substring in
this language, even if its period were less than six. None exists.
Therefore `G<=8p-1` for **every** p in the eight-row window. No corner
or parity-specific seed can make up this recurring loss.

As controls, 672 deterministic sample paths of lengths one to seven were
compared against direct physical-grid traversal with uncontracted rods,
including both forests and cycles. A five-block path recovered from
the exact transfer's predecessors was independently replayed as a forest.
These checks corroborate the representation; the exclusion is the
exhaustive sixth layer, not the sample. This does not prove strictness
uniformly in window height.

    cargo build --offline --release --bin equality_product
    python3 -B -m analysis.research_program.equality_product
