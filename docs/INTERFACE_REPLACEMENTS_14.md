# Exact replacement candidates on recorded 14-square boards

## Protocol, fixed before the run

Inputs: the score-76 trap, the board after the eleven recorded neutral
moves, and the resulting score-77 endpoint. All three are existing
development witnesses, not fresh held-out inputs. The prepared input is
reconstructed and each step literally checked; the final two-for-three
move must reproduce the recorded endpoint exactly.

For each input freeze all labels outside each region and free **all**
labels inside it. Enumerate every interior subset with the actual common
outside partition, as well as its discrete-port relaxation. Record the
best optional score at each actual cycle rank among relaxed forests.
Every candidate is also checked by the independent full-board Rust
traversal. There are no heuristic prunings or incomplete cases.

Generic region families:

* All 144 translated 3x3 windows.
* Sixteen 3x5 strips with x in {0,4,8,11}, y in {0,3,6,9}.
* All 66 pairs of twelve disjoint 3x2 tiles whose anchors have
  x in {0,3,6,9}, y in {0,6,12}. Pairs use one common exterior; some
  are adjacent, others separated.

Three trace-informed controls:

* The known final move's core rectangle [2,4]x[5,8].
* That core together with boundary vertex 10=(10,0).
* The 19-vertex symmetric difference of the original trap and endpoint.

The last control must admit the known score-77 endpoint when run on the
trap. It measures exact optimization on a known support; rediscovering
that endpoint is not a new escape mechanism. The core/tether comparison
tests whether the final local repair needs its distant boundary return.

All coordinates are zero-based. Each input has 229 regions and exactly
1,404,928 fillings: 73,728 compact, 524,288 strip, 270,336 pair, and
536,576 control fillings. Search stays at side 14 and at most 19 variable
vertices, within the existing limits. Run serially.

The test of a proposed cyclic replacement is Delta>2rho, where Delta is
its score change against the original filling and rho its actual cycle
rank. Positive relaxed gain alone is not a feasible improvement. Exact
enumeration of one region is not a whole-board upper bound.

## Posthoc supplier test

The main run found no improvement in any generic region. It recovered the
two expected control gains: trap plus its known trace support, and prepared
board plus core/boundary-10. The prepared core alone has optimum four,
unchanged from the original. This motivates a separate, explicitly posthoc
question: is boundary vertex 10 the only single outside hole that enables
the core to gain?

Keep the same prepared board and core [2,4]x[5,8]. For **every** original U
vertex outside the core, enumerate the core union that vertex, thirteen
variable labels. All other labels are fixed. Record every result, including
interior and boundary suppliers. This is a complete single-extra-vertex
family, not a claim about multiple extra vertices or arbitrary cores.

## Results

All runs completed without cutoffs. The main experiment checked 4,214,784
fillings over 687 regions; the supplier follow-up checked another 917,504
over 112 regions, for **5,132,288 fillings** in total. Every filling's
quotient feasibility was compared to the independent literal full-board
Rust traversal, including rejected candidates.

| Input | Compact gains / 144 | Strip gains / 16 | Paired gains / 66 | Control gains / 3 |
| --- | ---: | ---: | ---: | ---: |
| Original trap, 76 | 0 | 0 | 0 | 1 |
| Prepared board, 76 | 0 | 0 | 0 | 1 |
| Recorded endpoint, 77 | 0 | 0 | 0 | 0 |

Among the 678 generic regions, 506 have an apparent improvement in the
discrete-port relaxation. None survives actual exterior connectivity.
The largest apparent generic gain is three vertices. No positive-rank
candidate in any recorded rank profile satisfies Delta>2rho: even the
best such margin is at most -1. Both observed improvements are actual
rank-zero fillings in trace-informed controls, not a discovery of a
cyclic challenger with a profitable factor-two repair.

The original trap's trace-support optimum recovers the known nine-for-ten
replacement. The prepared board's core/boundary control recovers exactly
delete {73,101}, add {10,88,114}. Both reach 77. These are recovery checks
of existing gains; they are not new escape routes.

### Complete single-supplier result

On the prepared input, the core alone has maximum four F vertices,
equal to its original filling. Of all **112 original outside holes**, the
only one whose inclusion as an extra variable vertex raises the maximum
to five is **10=(10,0)**. Every other core-plus-one-hole region has optimum
four. In contrast, all 112 relaxed problems advertise an improvement.

An independent Python implementation exhaustively re-enumerated all
917,504 supplier fillings using adjacency traversal, confirming both
actual and relaxed feasible counts and optima. This is a complete finite
exclusion for this core and this fixed exterior. It is not a uniform
terminal theorem or an exclusion for multiple extra outside vertices.

### Exact terminal-path mechanism

The prepared board has F at 9 and 11, U at 10 and 24. Since 10 is on the
top boundary, promoting it adds exactly one forced edge, **10--24**: its
two horizontal incident edges are already forced by vertices 9 and 11.
The actual forced forest initially contains a unique 29-edge path from
10 to 24. Thus direct promotion creates a 30-edge cycle.

The neutral core exchange

    delete {73,101}, add {88,114}

leaves 76 F vertices and a forced forest, but puts 10 and 24 into distinct
components. The total forced-component count is **three both before and
after this neutral exchange**. Promotion at 10 then joins two components,
giving 77 F vertices and two forced components.

This proves a concrete distinction between component count and component
partition: the useful neutral change does not earn an extra c unit; it
changes WHICH terminals are connected. `interface_terminal_cut_14.json`
records the actual original path and the independently checked intermediate
board. The path argument is a direct finite graph proof, not an inference
from the rank-profile summaries.

## Research consequence

The generic small rectangles and selected two-window unions did not
produce a new challenger. The two-unit rank penalty also did not yield a
new positive certificate on these inputs. This does not refute larger
windows, other paired placements, or simultaneous low-K replacement
arguments.

A more specific next target is **score-preserving terminal separation**:
given a prospective promotion with one missing forced edge uv, determine
whether a neutral interface replacement can separate u and v in the
actual forced forest. For one missing edge, this separation is exactly
the promotion criterion. A boundary-conditioned solver can retain that
pair's connectivity as an explicit state and optimize subject to its
separation, rather than collapsing everything to total c or a worst-case
2rho price. Multiple missing edges need the complete star-root condition.

The example demonstrates this mechanism on a prepared input. It does not
prove that every unpaid moving interface admits such a neutral separator,
nor pay height-weighted terminal demand in the global paper program.
The global constant-gap bounds and geometric pump question remain open.

Follow-up: `TERMINAL_SEPARATION_14.md` tests every interior 3x4/4x3 core
on eleven inputs. The simple neutral-refill claim is refuted: 113 of
114 separable cores require a one- or two-vertex loss. A uniform two-loss
separator lemma survives, and actual immutable paths exclude every
interior-only repair for 30 of the 32 eligible terminals with their
neighbourhoods and the boundary fixed.

## Verification and reproduction

* Rust library: **48 passed, one pre-existing expensive test ignored**.
* Release build, rustfmt, and whitespace checks passed.
* Python independently checked all 5,467 main-run rank-profile witnesses
  and all reported best fillings. This main audit is a witness audit, not
  a second exhaustive main search.
* Python exhaustively re-enumerated the supplier study and checked its
  1,179 saved rank-profile witnesses.
* No Lean work or optimization above side 14 was performed.

Artifacts:

* `data/interface_replacements_14.json`, SHA256
  `1168680c7a0a07a75a59b93867828af53bea8cd044347eef5669d312c4874697`.
* `data/interface_replacements_14.audit.json`.
* `data/interface_suppliers_14.json`, SHA256
  `f0ef14ebfdb00cf0e1cf4621087aad5b38401efa06086eee301d036837b54f34`.
* `data/interface_suppliers_14.audit.json`.
* `data/interface_terminal_cut_14.json`.

Use fresh output paths; all drivers refuse to overwrite results:

```bash
cargo run --release --bin interface_replacements -- /tmp/opencode/replacements.json
cargo run --release --bin interface_replacements -- /tmp/opencode/suppliers.json suppliers
python3 -m analysis.interface_fillings.replacements_audit /tmp/opencode/replacements.json /tmp/opencode/replacements.audit.json
python3 -m analysis.interface_fillings.replacements_audit /tmp/opencode/suppliers.json /tmp/opencode/suppliers.audit.json --exhaustive
python3 -m analysis.interface_fillings.terminal_cut /tmp/opencode/replacements.json /tmp/opencode/terminal-cut.json
```
