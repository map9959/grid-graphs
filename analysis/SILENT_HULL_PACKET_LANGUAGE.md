# Silent-hull row-packet language

`residue_two_silent_hull_language.py` proves the following exact conditional
coverage lemma for every width `n=3k+2`.

> If every face cut of a rooted frontier is crossed by at most one non-OUT
> occurrence hull, then the frontier has a lossless left-to-right encoding with
> one active carrier, finite packet atoms, and affine counters. A carrier may
> cross a packet without occurring in any face of that packet.

The decoder is a finite-control scan. Its non-finite values are only the packet
length, fresh-component count, and additive cost/rank/cycle counters. For an
exact source/action/target triple, `certify_silent_hull_transition` checks the
row successor and derives

```text
rank_delta = new_faces + source_components - target_components
cycle_delta = horizontal_edges + vertical_edges - rank_delta
weight = 3 * row_U - 2 * rank_delta - 1.
```

Thus every accepted certificate is sound for the exact row semantics. The
complete `n=5` equality corridor and every transition of the exact silent-gap
`n=11` equality witness are regression-checked; row 8 contains the required
silent atom.

`certify_silent_hull_symbolic_transition` checks a proposed
source/action/target word with a bounded streaming product. It retains OUT, the
old/new faces at the packet cut, one source and target carrier, and the finite
actual-to-expected incidence relation. Liveness is closed across that relation
before components are forgotten. Silent atoms preserve the active carrier
without requiring a local occurrence. Rank, cycle, and charged-weight counters
are derived from local bits and component counts; the certifier does not call
`advance_row`.

This proves soundness of every admitted symbolic source/action/target word. A
separate closure theorem must still show that every relevant codec source and
action has a represented successor.

The normalized product rejects irreversible incidence fan-out immediately.
Every surviving component is tied to one of four actual or three expected
physical cut ports, so each side has at most seven live components independent
of packet length. Row-dependent face shape is validated as part of the codec;
an absent frontier is legal only at the top or terminal row. The invariant and
remaining completeness statement are detailed in
`SILENT_HULL_TRANSDUCER.md`.

This does not prove universal obligation 7c.5. The remaining exact coverage
lemma is:

> Every frontier on a hypothetical connected residue-two path with terminal
> charged curvature `K<=2` has face-cut occurrence-hull width at most one (or
> admits a finite extension of this scan control).

No finite-width observation establishes that statement.

`residue_two_first_defect_certificate.json` now monitors first entry into this
codec boundary on every complete path at `n=5,8`. No `n=5` path has a codec
defect. At `n=8`, the minimum complete path whose first defect has face-cut
width two has curvature eight, a gap of three above the curvature-five minimum.
The defect occurs first at row 7 in the deterministic witness. All 461,624
codec-valid completable `n=8` edges pass the bounded streaming topology and
local-counter certificate. Exact edges are enumerated with `advance_row`, but
their certification is independent of that oracle. This is still a fixed-width
first-entry theorem, not arbitrary-word closure. The silent-gap `n=11` control
remains codec-valid and symbolically certified at every row.

The held-out width is now complete for the codec question.
`residue_two_n11_face_cut_defect_result.json` records an exact two-channel Rust
optimization with no beam or symmetry reduction. At U limit 72, every optimum
path is codec-valid. At limit 73, the first codec-defective path appears, with
curvature eight and first face-cut width two at row 7. Thus `n=11` has the same
three-unit first-defect gap as `n=8`. This remains fixed-width evidence.

`residue_two_silent_hull_certificate.json` records an independently checkable
integer potential on the complete `n=5,n=8` augmented history languages plus
the exact `n=11` silent path. All 794 represented transitions are tight under
`weight + Phi(target) - Phi(source) >= 0`, with initial potential zero and every
represented terminal anchored at `-5`. This is an exact finite-language result,
not universal coverage.

The separate formula

```text
Phi = -3U + row + 2faces - 2debt
```

is exact accounting, not a lower-bound potential. Since
`rank=faces-debt`, every exact transition has
`weight+Delta(Phi)=0`, and a connected terminal has `Phi=-K(U)`. Therefore
coverage plus this identity alone would telescope only to `K=K`. A universal
proof additionally needs a noncircular theorem that every accepting symbolic
terminal has minimum accumulated weight at least five.

The first structural potential CEGAR steps are exact but negative.
`residue_two_cut_potential_obstruction.json` rules out scalar packet-cut
potentials using repeatable weight-`-1` self-loops. The atom-sum equality model
is inconsistent, and the adjacent-bigram model has an exact edge contradiction
`-3>=0`. The richer finite-parser word model is also exactly infeasible: its
transformed constraints contain an independently verified `-1>=0` Farkas
contradiction. A one-step incoming-history refinement was not retained because
materializing its augmented product exceeded the workstation memory budget.
