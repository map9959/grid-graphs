# The comb remains exact with an unbounded free L at two adjacent sides

For `n=3k+1≥88`, keep only the following marks prescribed in the
rectangle `R=[0,n-8]×[6,n-1]` (row, column coordinates inclusive):

* the top is a marked bar; row 2 and the bottom of `R` have the rail
  profile `x=0 mod 3` within `R`;
* column 6 of `R` is marked except at row 1.

Every other mark, including the entire western six columns and southern
seven rows, may vary. The maximum is exactly the ordinary comb score.
In particular the two partial profiles need not continue across the
western arm.

**Straightening.** The top bar forces its neighboring row in `R` empty.
It wires the upper terminals of the [arbitrary-height seam](UNBOUNDED_RAIL_SEAM.md)
in the width-`n-6` rectangle. If `m` lower-terminal components are not
in that wired tree, the seam bound `M+m≤H((n-6+2)/3)` gains at least
`m` marks upon replacing its interior by regular rails. On the western
interface every vertex already lies in the wired component (including
the empty row-1 site); at the bottom every site is a terminal or its
lateral leaf. Thus the replacement keeps the interface marks and just
identifies the other `m` classes with the wired one. Adding these `m`
links to the external forest creates at most `m` independent cycles.
Each resulting cycle crosses the free L along a path between two core
contacts. No external site has two core neighbors. A path must turn
outside: on a straight ray leaving this convex rectangle it cannot
reenter. At a turn an incident edge has a unique owner (otherwise
there is a diagonal marked pair). If the turn is at the entering site
and its predecessor is marked, the first tangential edge must have an
external sole owner. Hence one can remove an L mark to break the cycle;
repeat until acyclic. This is the terminal-class surgery from the
seam theorem, with the western contacts all wired as well.

**Exact L price.** After straightening, the core is one forced tree.
Contract it, retaining every edge from it to the unknown L (parallel
contacts count separately), mandatory when its core endpoint was
marked. Sweep down the western arm and then east along the southern
arm. The exact max-plus frontier vector repeats after 30 western rows
with score shift 60 and after 30 southern columns with shift 73.
`elbow_pump.py` checks the full normalized vectors, not just the
maxima, on all ten starting widths 88 through 115. In the western
straight stretch each row has the same six-site step and a mandatory
edge to the contracted west rail. In the southern straight stretch
each column has seven sites and its terminal edge is mandatory on
one of three column residues. Neither elbow nor end changes under
these insertions. Thus the recurrences iterate at the same time.
The core has `(n-6)+(n-9)((n-6+2)/3)` marks. Adding its growth to
the two shifts gives the comb growth. At 103 the core contributes
3199 and the L contributes 447. The actual comb supplies equality.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.elbow_pump
```
