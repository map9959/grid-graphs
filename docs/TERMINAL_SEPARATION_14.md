# Exact neutral terminal separation: protocol

## Questions fixed before the run

For a hole v with exactly one hole neighbour w, promotion adds exactly
one forced edge vw. During refilling keep v labelled U and every neighbour
label fixed; afterwards change only v to F. A feasible replacement
permits promotion precisely when v
and w are in different actual forced components.

Test the candidate claim: **if clearing a small interior core separates
v from w, can the core always be refilled to its original score while
keeping them separated?** Clearing means making every core vertex U.
The score requirement is essential; a separator that loses one F merely
breaks even after promotion. A counterexample refutes this small-core
claim, not a claim about unspecified larger regions or all low-K maxima.

Inputs: the recorded trap76, prepared76, endpoint77, plus all eight fixed
`data/shuffle_study_14/input_XX.txt` boards. These are reused research
inputs, not a fresh held-out benchmark. The prepared case is a positive
control, and the 77 endpoint a negative control. Read the three original
boards from the previous frozen replacement artifact.

For each input enumerate every fully interior 3x4 and 4x3 rectangle
(180 rectangles per board). For every initially blocked one-edge
promotion, test that rectangle if it avoids v and every neighbour of v.
Thus the prospective edge and all other incident labels stay fixed.
These geometric candidates are independent of the known repair core.

For each compatible pair retain the maximum core F count subject to
forced-forest feasibility AND separation. Also retain an exact-neutral
witness if one exists, and verify its promoted board independently.
Record how many labels it changes and the actual component counts.

If v,w remain connected even after clearing the core, that path survives
every filling: report a complete monotonic obstruction. Otherwise enumerate
every subset of the core (4096), sharing the enumeration across terminals
for that core. Compare quotient feasibility with literal full-board
traversal and test separation using actual components. No virtual bank
connections, heuristic pruning, or time/node cutoffs.

The proposed finite claim is falsified by any separable cleared core
whose maximum separated filling has fewer F than the original core.
Success means an exact-neutral separator, hence a verified gain after
promotion. Also measure complete separator deficits and whether gains
generalize beyond the prepared control. Search stays at side 14.

## Completed results

The 11 boards supply 32 initially blocked one-edge terminals. All 1,980
geometric cores were considered, yielding **5,688 compatible core/terminal
pairs**. Clearing the core leaves the terminals connected in 5,574 pairs:
these have a complete surviving-path exclusion, not an enumerative cutoff.
The remaining 114 cores were exhaustively enumerated, **466,944 fillings**.

| Input | Compatible pairs | Separable by clearing | Optimal loss 0 | Optimal loss 1 | Optimal loss 2 |
| --- | ---: | ---: | ---: | ---: | ---: |
| prepared76 | 708 | 63 | 1 | 53 | 9 |
| comparison_03 | 530 | 51 | 0 | 36 | 15 |
| Other nine boards combined | 4,450 | 0 | 0 | 0 | 0 |
| Total | 5,688 | 114 | 1 | 89 | 24 |

Here loss means original core F count minus the maximum separated core
F count; the promotion has not yet been added. The sole neutral separator
is the known prepared core [2,4]x[5,8], deleting {73,101} and adding
{88,114}, followed by promotion at 10. There is no new score-77 witness.

**The proposed neutral-refill lemma is false**, including on score-76
inputs rather than just the 77 negative control. The weaker proposed
one-vertex-loss guarantee is false as well. These counterexamples do not
refute a lemma with additional low-K or unused-resource hypotheses: the
present boards do not instantiate the hypothetical global low-K regime.

### Explicit exact two-loss example

On prepared76, take the fully interior core [4,6]x[1,4] and terminal
v=10=(10,0), w=24=(10,1). Its original core has three F vertices, at
46,47,48. Clearing it separates v,w. The exact maximum under separation
is **one**, so the loss is two even allowing arbitrary rearrangement of
every core label. Deleting 46 and 47 already achieves a separator with
one F retained. All 4,096 fillings were checked independently in Rust
and Python. The complete surrounding board and best filling are archived
in `terminal_separation_14.paths_and_boundary.json`.

## The uniform statement that does survive

**Two-vertex separator lemma.** Suppose H(F) is a forest, v,w are connected,
and changing every F label in a free region S to U disconnects them. Then
one can disconnect them by deleting at most two F labels in S. Therefore

    max separated core score >= original core score - 2.

**Proof.** H(F) has a unique v--w path. At least one of its edges is
absent after clearing S. Every currently F endpoint of that edge must
lie in S, otherwise the edge would still be forced. Delete those F
labels, at most two. The edge disappears, hence the unique path is cut.
The remaining graph is a subgraph of the original forest. This preserves
all prescribed labels outside S. The two-loss finite example above
shows that refilling cannot universally improve the coefficient two.

This is the same physical FF-edge issue found in the earlier rank-price
lemma, now localized to one actual terminal path. It is a direct paper
proof, not a Lean formalization. A subsequent independent mathematical
review in batch001 accepted the uniform arguments and requested the
frozen-label wording clarifications now incorporated above.
The path extractor independently constructs the one- or two-deletion
separator for every one of the 114 separable cases.

For a *global maximum* and a compatible one-edge promotion, a neutral
separator would improve the board. Thus, when clearing S separates the
terminals, its optimal separator deficit must be exactly one or two.
If the original path has a removable FU edge whose F endpoint lies in S,
deleting that endpoint gives a one-loss separator, forcing deficit one
in a global maximum. These are necessary local conditions, not a global
upper bound or permission to spend the same loss repeatedly.

## Stronger whole-interior obstruction (posthoc)

To distinguish a small-core limitation from an immutable boundary path,
clear **every interior vertex except the fixed closed neighbourhood of
the terminal**, keeping the complete physical boundary unchanged. This
is a single graph check per terminal, not an optimization on 144 variables.

For **30 of the 32 terminals**, v,w remain connected. The archived surviving
path consists of edges that are forced even in this fully cleared state.
Every other admissible interior filling retains them. Hence **no interior
replacement of any size** can enable that promotion with its neighbourhood
and the outer boundary fixed.

The only terminals without this global interior obstruction are the
tested ones on prepared76 and comparison_03. The latter still requires
one or two lost vertices in every tested small core. This does not rule
out a larger neutral separator for that terminal.

Consequently merely enlarging interior rectangles cannot help the other
30 terminals. Further replacement attempts there need a boundary change
or a different promotion whose local incident labels are allowed to
change. For the two accessible terminals, a zero-cost refill still needs
an additional structural or accounting hypothesis. Disconnection after
clearing alone is insufficient to guarantee a neutral refill.

## Verification and artifacts

* The independent Python audit reconstructs all terminal lists, all 180
  cores per board, and their compatibility; checks every monotonic
  exclusion; and independently enumerates all 466,944 candidate fillings.
  It verifies exact optimum scores, neutral masks, and promoted witnesses.
* The Rust regression test exhaustively compares separator optima with
  literal full-promotion feasibility on every feasible 3-square board
  for three test regions.
* Rust library: **49 passed, one pre-existing expensive test ignored**.
  Release build, formatting, and whitespace checks passed.
* All work stays at side 14. No Lean changes, new global bound, or pump.

Files:

* `src/terminal_separation.rs`, `src/bin/terminal_separation.rs`.
* `analysis/interface_fillings/separation_audit.py`.
* `analysis/interface_fillings/separator_obstructions.py`.
* `data/terminal_separation_14.json`, SHA256
  `3de0212a22b7c8a53fa191c95a6dee63f377ce5fdde2fbf87c9ef4436c31cbc1`.
* `data/terminal_separation_14.audit.json`: independent exhaustive audit.
* `data/terminal_separation_14.paths.json`: first path extraction.
* `data/terminal_separation_14.paths_and_boundary.json`: extended path
  extraction including whole-interior exclusions; earlier output retained.

Use fresh output paths:

```bash
cargo run --release --bin terminal_separation -- /tmp/opencode/separation.json
python3 -m analysis.interface_fillings.separation_audit /tmp/opencode/separation.json /tmp/opencode/separation.audit.json
python3 -m analysis.interface_fillings.separator_obstructions /tmp/opencode/separation.json /tmp/opencode/separation.paths.json
```
