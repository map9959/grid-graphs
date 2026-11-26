# Nine free rows: a strict period-independent bound by rod ownership

For local rows `-3..5` in the three-column sheared-pocket model,
`G <= 8p-ceil(p/5)` for **every** repeat period p. Hence
`b+R+t >= p+3*ceil(p/5)>p` by the exact shear ledger. This is a
computer-assisted inequality for this geometry, not a global square bound.

The [height-free flux certificate](HEIGHT_FREE_ROD_FLUX.md) subsequently
proved the same inequality at arbitrary fixed pocket height using a
single local current table.

## Why a rod can be charged only once

Contract the immutable rod stars and keep the core and frame as disjoint
edge sets meeting at the two rod vertices per triple. In the periodic
quotient a feasible component is a tree or unicyclic with nonzero
winding. Orient a tree toward a root; orient a unicyclic component
toward and around its cycle. Each vertex spends at most one outgoing
edge. Lift this orientation before cutting open any finite interval
of blocks. Write M for the number of rods per repeat whose outgoing edge
is in the core. No such rod can spend an outgoing edge in the frame.
A rod with no outgoing edge in either region may conservatively be
treated as available to the frame.

In either restricted region, designate a rod with no outgoing edge
there as a sink. A connected finite tree cannot contain two sinks:
with q vertices it has q-1 edges to orient, which need q-1 distinct
sources. This reasoning applies to any finite connected subgraph of
the lift, not just entire quotient components. Identifying all designated
sinks with a bookkeeping vertex ("ground") is therefore a necessary
acyclicity test on any finite interval: distinct grounded rods have no
path between them. Conversely, dropping external incidences or forgetting
components may relax this test and cannot strengthen the upper bound
spuriously. The ground is not a physical graph vertex or a new payment.

## Two certificates using the same M

* **Frame:** on one side, keep the last three lane vertices, their mask,
  the common ground and the partition. During a triple introduce the
  rod; ground it if it is designated unavailable. Add every forced edge,
  including all the U-port contacts, reject cycles, then forget the rod.
  Weight the step by its number of frame centers plus one if grounded.
  `frame_root_price.py` checks a potential on 21 reachable states and
  1,138 three-column transitions bounding this weight by four plus a
  telescoping difference. The bottom is a translated phase of the same
  strip. Ground the M core-used rods in their respective frames.
  Summed over both sides, **N+M<=8p**.
* **Core:** enumerate the free 27-site packet masks, rejecting forced
  cycles. In each triple independently choose which of its A and B rods
  are unavailable to the core (the complement of the M used rods).
  Reject any packet already connecting two grounded rods. In its
  physical left/right profiles retain a common ground plus the selected
  ports and their component partition. Across a block boundary add all
  actual forced edges. Reject cycles and joins that would connect the
  left and right ground groups before their identification. The new
  profile factorization retains necessary within-pair tests; it can
  forget distant connections. Weight a block by its selected core sites
  minus nine minus the number of rods available to the core. With the
  designation from the orientation the sum is exactly delta-M.

  The normalized max-plus vector recurs with a **negative** shift:
  `-1 per 5 blocks`. A potential obtained from this orbit is then checked
  on every transition after maximizing over the preceding half-step:
  309,641 block options and 21,563,140 compatible joins. Its telescoping
  bound is **5*(delta-M)<=-p** on any closed sequence. An unrolled
  interval loses only a bounded endpoint term.

Adding eliminates M. The previous split-price test would not establish
this result: on the same rows its relaxed `delta+splits` maximum is 4
per 3 blocks instead of at most 3. Overestimating splitting in a local
window does not create a second outgoing slot on the rod.

## Independent check and controls

`grounded_core.rs` sweeps the same nine-row band one column at a time.
The state holds the selected frontier mask, a single live partition
including both rods and the ground, and the remaining physical ports.
On a change of triple it retains the ground, introduces the next two
rod choices and shifts normal coordinates by three. Every new edge is
tested against the existing full partition, rather than two separate
profiles. The full 35,707-entry terminal vector recurs with the same
shift `-1 per 5 blocks`. No SAT UNSAT conclusion is used here.

| verified p | frame N | core-used rods M | core delta | G | integer upper |
|---|---:|---:|---:|---:|---:|
| 2 | 16 | 0 | -1 | 15 | 15 |
| 3 | 24 | 0 | -1 | 23 | 23 |

For the controls the program orients the actual witness quotient by
leaf removal and cycle orientation, then counts M and verifies both
inequalities. Open-board forest replays remain separate. Since equality
at `8p` fails in the growth rate, there is no target repeat in this
window to reconstruct or pair with a seed.

    python3 -B -m analysis.research_program.frame_root_price --witnesses
    python3 -B -m analysis.research_program.shear_packets -3 5 --unit --ground --critical
    cargo build --offline --release --bin grounded_core
    target/release/grounded_core 12
