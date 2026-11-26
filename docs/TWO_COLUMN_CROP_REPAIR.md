# Two adjacent free columns at every moving-core step

Use the `Q_k` crop of `MOVING_CORE_FRAME_RATE.md`, with any fixed number
of unmodified end triples large enough that the free rectangles do not
meet the crop boundary (five suffice below). At each other index j all
F/U choices in a two-column rectangle may change **independently** of
the other indices. Outside the rectangles the crop is fixed. All labels
in the surrounding three-layer frame are free. This is not a restriction
to a single motif applied identically.

### Two placements

Use local row `r=row-3j`, column `c=col-3j`. In the original crop the
top rod on c=1 ends at r=0, bottom rod on c=0 starts at r=2, and there
is a singleton at (2,2).

* In placement A, release columns **1,2** on `lo<=r<=hi`. This erases
  `2-lo` old centers: the top rod tip and the singleton. The bottom rod
  remains intact. The free satellite column of the previous test is now
  accompanied by a fully free adjacent rod column, not just a trim bit.
* In placement B, release columns **0,1** over the same rows. This time
  both rod tips are free and the singleton remains fixed. The debit is
  `hi-lo` centers. These are two separate all-index experiments; arbitrary
  mixtures of the two placements are not claimed.

### Interface and objective

Contract the forest of the remaining fixed rods. For A the separator is
c=0. Keep the roots of the top and bottom rods and each individual site
`r=lo,...,0` on that separator; sites above/below this interval already
belong to a root. Keep the translated copy at the right separator c=3.
A promotion in each neighboring packet can force edges to the **same U
site** on this column. Identifying only top and bottom roots and forgetting
this site would miss that connection. For B the separators are c=-1,2.
On the left keep the preceding top rod, current bottom rod and the
intervening separator sites `r=lo-3,...,hi`. The fixed singleton and its
two vertical contacts already form one component. Identify that set
only once, not a second time when gluing the next rectangle.

For each free mask add every physical edge incident to a selected center.
Deduplicate an edge selected from both ends but retain distinct edges
between the same contracted components. Reject cycles. Among forests
with the same partition of the two separators save the largest
`selected centers - original centers`. A connected tree on t distinct
interface vertices has the same effect on future cycle tests as t-1
unions; components not meeting the interface need no state. Thus the
maximization is only between genuinely equivalent boundary data.

Jointly process three columns on the top and bottom frame as in the
previous crop transfer. Use the appropriate live rod for each actual
port, including a U contact if its adjacent frame site is selected.
Merge the pocket partition into the frame partition, rejecting repeated
unions. Forget the left ports only after this merge. The objective adds
the six-lane frame score and the net core change. The outside side strips
contribute at most `6k+O(1)` as before, with only O(1) omitted end blocks
and corners. To achieve `14k+25` net centers a repeating interior must
therefore supply **8 per block** in this joint account.

### Verified results

For A with `lo=-3,hi=5` (nine rows by two columns) all 262,144 masks
yield 128 distinct feasible interface signatures; the largest single
packet delta is zero. A second enumeration builds the actual grid stars
and checks `edges = vertices - components` by traversal. Its table of
maximum net scores agrees on every signature, including all separator
U contacts. Joint frontier maxima for 1..6 blocks are 8,16,24,32,39,47.
The fourth and sixth vectors have identical 11,880 keys and every
entry increases by exactly 15. The same block operator applies at each
step and commutes with adding a constant; induction gives rate **15/2**,
not 8. This bounds the whole score by `13.5k+O(1)` in the net frame
account. A `lo=-1,hi=4` control also has rate 15/2 on 2,306 states.

For B with `lo=-1,hi=4` there are 52 feasible signatures, net maxima
8,16,23,30,37, and a one-block shift of 7 on 3,464 terminal states.
A physical B edit in the larger rectangle on the side-14 crop deletes
`(6,3),(7,3),(8,3)` and adds `(5,4),(7,4)`. It takes 69 to 68 centers,
preserves forest feasibility, and disconnects top port `(0,7)` from
bottom port `(13,3)` (previously connected). Separating these ports
is possible; separation by itself does not establish a target renewal.

For B at the larger `lo=-3,hi=5` extent, an alternative certificate
avoids a large joint transfer. There are 526 pocket partitions on 14
ports per separator. Record whether the **left** satellite is connected
to the current top rod and the **right** satellite to the current bottom
rod. The maximum local net center changes at the four combinations are
`neither:-2, left only:-1, right only:-1, both:0`. If neighboring
incidences of a satellite are both present the corresponding top and bottom
roots are necessarily connected. Thus every actual separation costs at
least one core center when the packet debits are summed (a missing
incidence belongs to exactly one satellite). Ignore all additional
connections to favor the frame. Then frame plus core delta is at most
frame minus split count, whose exact 516-state vector shift is 7 per
triple in `modified_crop.py`. This proves the net rate bound of 7
even for the larger two-rod window; no extrapolation from a partial
large-state run is used.

    python3 -B -m analysis.research_program.double_pocket -3 5
    python3 -B -c 'from analysis.research_program.double_pocket import audit; audit(-3,5)'
    python3 -B -m analysis.research_program.double_pocket -1 4 --rods
    python3 -B -m analysis.research_program.double_pocket -3 5 --rods

These bounds do not treat unbounded-height rewrite regions, fully free
three-column packets, a different exterior rod pattern, or general trees.
