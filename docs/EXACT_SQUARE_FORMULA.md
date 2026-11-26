# Exact full-degree spanning-tree count on a square

**Lean theorem.** Import `GridGraphs.Results.SquareFormula`.
`GridGraphs.maxPreserved_square_exact` proves the formula below for every
positive side, with no fan-exclusion premise. In particular,
`maxPreserved 161 161 = 8791`. The [fan proof](ONE_GAP_FAN_LEAN.md)
describes the two last exclusions.

Write `n=3k+s`, `s=0,1,2`. For positive sides the matching lower and
upper values of `P(n,n)` are:

| `s` | range | value |
|---|---|---|
| 0 | `k≥1` | `3k²+3k−2` |
| 1 | `k≥5` | `3k²+5k+floor((3k−13)/10)` |
| 2 | `k≥6` | `3k²+7k−floor((k−5)/7)−[n ≡ 35 mod 42]` |

The omitted residue-one sides `1,4,7,10,13` have values `1,8,22,42,68`.
The omitted residue-two sides `2,5,8,11,14,17` have values
`2,11,27,49,77,110`. See the [small exact table](../analysis/conjectures.md#updated-diagonal-data-phase-7a)
and the [independent upper at 17](THREE_SQUARE_JOINT_CUT.md).
For residue zero see [the square dual](EXACT_RESIDUE_ZERO.md); for
residue two see the [construction and classification](RESIDUE_TWO_CLASSIFICATION.md).

## Residue one: splitting the maximum into two exhaustive cases

The [four-row comb](FOUR_ROW_COMB_CAP.md) is a physical lower witness.
If the maximizing tree has a pitch line, cut there and apply the
[uniform cap certificate](UNIFORM_PITCH_CAP_PRICE.md). If it does not,
suppose for contradiction that it beats the comb. The physical map to
the [free-count face and line ledger](FREE_FACE_LEDGER_103.md) applies
verbatim with `m=k+1`, baseline `nm`, four local corner labels and no
restriction on total join rank. Its local refill exclusions require
maximality, which is why the dual is applied to a *maximizer*. The
nonempty-stub premise holds since `m²+2k²` is at most the comb.

On both progressions `n=58+6u,61+6u`, `u≥0`, exact dual summation
gives the conditional upper

```
3k² + (21/4)k − 79/64 .
```

Subtract this from the *unrounded* comb expression. The difference
is `k/20−21/320`, positive throughout these progressions. An
integer strictly above the attained comb therefore cannot satisfy the
no-pitch dual either.

## Why the no-pitch prices transport

`free_width_dual.py` replays two rational vectors, with 3,625 and 3,552
entries. They were recovered from LP bases but replay does not optimize.
It checks every multiplier sign and every non-fixed reduced cost, with
**zero** positive residual. Width transport has two separate parts:

* **Columns.** The fine types are those of the [diagonal chart](DIAGONAL_SECTOR_UPPER.md#exact-counting-not-fitting-values):
  boundary depth 8 for sites and 7 for patch origins, period three in
  each bulk axis, signed diagonal distances clipped at 9. They determine
  all incident coarse patch and star roles and all eight symmetry
  images. The older sector matrix is generated once per parity.
  For the added rank faces, each child patch origin fixes its offset
  in the face (its two residues), and its fine axis labels fix the
  depth-two parent labels after subtracting that offset. Thus a new
  position cannot create a new child/parent pairing. The face words,
  local partitions and shared-edge incidences are independent of side.
  A horizontal transition sees just the preceding and current depth-eight
  axis labels; these determine the adjoining depth-two faces and which
  of their edges is read. Growth only inserts repeated interior junction
  labels. The reachable line-DFA states stabilize by the fifth letter
  under an interior update (checked directly). The first three junctions
  have boundary labels; both bases already include interior-to-interior
  transitions after stabilization. Thus enlarging the board introduces
  no new arc, including at either boundary. Identical occurrences are
  counted in the *variables*, not as new coefficients.
* **Right sides.** Only normalization masses, rank/score budgets and
  axis-band bounds depend on width. The fine bucket masses are quadratic
  in `u` by exact lattice-interval summation in `chart_counts.py`.
  Replay sums all the bucket polynomials at each base, for both squares
  (sites and patch origins); they exhaust `(S+6u)²` identically, so
  no missing type appears later. The other nonconstant bounds are
  `2m²`, `nm`, `nm−1`, or signed products of `m−1` and an axis-label
  multiplicity. That multiplicity is constant at an end and affine
  in the bulk. All other right sides are constant. Consequently the
  **same rational linear combination** has degree at most two.
  Replay checks its three coefficients by evaluation at `u=0,1,2`,
  and compares the actual coefficient matrices there as a cross-check.
  This uses polynomiality of the certificate, not polynomiality of an
  LP optimum.

## Finite base cases and replay

Below 58 the unrestricted exact results at sides
`16,28,31,34,37,40,43,46,49,55` already agree with the formula:
see the small table above, [28](RESIDUE_ONE_STRIP_CUT.md),
[31–43](RESIDUE_ONE_WITNESS_EXTENSION.md), [46–49](FOUR_ROW_COMB_CAP.md)
and [55](DIAGONAL_SECTOR_UPPER.md). The four remaining sides are
covered by direct finite charts, without any width extrapolation:

| side | no-pitch dual upper for an above-comb maximizer | physical tree |
|---:|---:|---:|
| 19 | `1478356517/10718111` | 138 |
| 22 | `268230743299/1472335032` | 182 |
| 25 | `2325130462927/10000000000` | 233 |
| 52 | `61121/64` | 955 |

The 25 replay charges all positive residuals at `n²` per unit; the
other three have no positive residual. Each upper is strictly below
the next integer after the witness. The pitch argument covers the
complementary case.

```
python3 -B -m analysis.research_program.free_width_dual
python3 -B -m analysis.research_program.slit_width_induction --prove
python3 -B -m analysis.research_program.slit_width_induction --prove --vertices
python3 -B -m analysis.research_program.comb_cap_transfer --period
```

These are computer-assisted proofs. The final arithmetic implications
are also checked in Lean; the automata and LP physical maps are not
claimed as end-to-end Lean formalizations.

## Lean formalization status

`GridGraphs.Results.ExactSquareFormula` defines the executable `squareScore`
and the statement `ExactSquareFormula` about the graph maximum. It proves
the three residue simplifications, equality for sides 1–5, 7 and 10, the
entire residue-zero lower bound, and an exact-size mask criterion for the
remaining graph equality. `squareScore_comb_word` supplies an explicit
accepted four-row cap word of the required length and total score for every
`k≥5`: the checker merges components for each column, checks ten suffixes,
and proves an exact 30-column loop at the same seam state.
`GridGraphs.Constructions.CombMergeSound.fold_merge_sound` proves that
each accepted list of edge insertions preserves actual graph acyclicity
when its port labels extend to component labels.

`GridGraphs.Results.CombLower` now proves the **graph-theoretic
residue-one lower bound at every width**. `CombColumnSound` freshens
four isolated sites and relabels the entire graph when retiring ports;
`CombSweep` iterates this invariant without deleting old edges.
`CombRails` implements the two physical rail components on row/column
coordinates (the attachment vertices can change between columns).
`CombCoverage` embeds the square's graph of forced edges into the
resulting forest. Finally `squareMaskScore_comb` counts the marked
set at `k≥5`, and `squareScore_lower_residue_one` includes all the
small sides. Replay: `(cd lean && lake build GridGraphs.Results.CombLower)`.
`GridGraphs.Results.PitchUpper` also proves the **physical residue-one
pitch upper** for all `k≥5`, including boundary and transposed cuts.
`GridGraphs.Tests.CapSiteTableReplay` discharges its two closed table
checks. See the [physical trace construction and replay](UNIFORM_PITCH_CAP_PRICE.md#lean-replay-and-the-physical-cut).
`PitchCut.exact_of_no_pitch` reduces stable residue-one equality to the
remaining no-pitch bound on maximizing physical mark sets. The universal
all-residue equality is not yet a checked Lean theorem.

For the no-pitch case, `PhysicalFaceLine.pooled_overlap` (Lean name
`GridGraphs.NoPitch.pooled_overlap`) proves the face/line marginal before
identifying symmetry-equivalent columns. The face mask, global skeleton
corner connections, and the adjacent pair of line states all come from
one mark set. `shared_boundary` includes the cut bit on a shared edge.
The decoded columns now carry their canonical atom keys and stabilizer
multiplicities. `NoPitch.Dual.physicalVector` maps the physical stars,
3×3 patches, rank faces, line transitions in all eight views, and
complete-line auxiliaries to these column IDs. A missing key receives
no mass. `GridGraphs.Tests.PhysicalColumnReplay` checks invertibility
of the column dictionary and completeness for **occupied stars** at
sides 19, 22, 25, 52, 58 and 61. Its `width_objective` gives exactly
eight times the mark count for every acyclic physical set at those sides
and any in-bounds parent directions. This completeness check does not
prove that every maximizing face passes the chart's refill filter.
`physical_finite_upper` applies the finite duals at the first four
sides, conditional on feasibility of this specific vector.
`TailCoverage.covers_step` now transports occupied-star coverage from
`k` to `k+2` for all `k≥19`, and `objective_tail` proves the eightfold
physical score throughout both tails. `physical_tail_upper` combines this
with the dual. Its remaining premise is feasibility of the physical
vector, including the forest budgets.

```
(cd lean && LEAN_NUM_THREADS=2 lake build GridGraphs.Tests.PhysicalColumnReplay)
```
