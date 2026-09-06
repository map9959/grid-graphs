# Residue-two universal-bound certificate boundary

For `n=3k+2`, let `U` be the non-full vertices and let the dual graph formed by
all `U-U` grid edges be connected. Write `rho` for its graphic rank, `R` for
the total number of row and column `U`-runs, and `beta` for its cycle rank. The
exact identities give

```text
rho = (n-1)^2
K(U) = 3|U| - 2rho - n = 2R + 2beta - |U| - n.
```

The old residue-two baseline is therefore exactly the curvature-five claim:

```text
K(U) >= 5
<=> 3|U| >= 2(n-1)^2+n+5
<=> |U| >= 6k^2+5k+3.
```

There is also an exact forced-forest component decomposition. Put
`F=V(G)\U` and `H=G-E(G[U])`, and let `c_F,c_H` count the components of
`G[F]` and the spanning forest `H`, including isolated vertices. If `Q_U`
counts boundary-side incidences of U, then

```text
K(U) = Q_U+c_F+c_H-n-2.
```

Hence the universal first step `K>=2` is exactly
`Q_U+c_F+c_H>=n+4`; obligation 5 is exactly the stronger residue-two bound
`Q_U+c_F+c_H>=n+7`. This retains the component terms lost by raw edge and
boundary counts. The identity and known controls are independently checked by
`residue_two_obligation5_components.py`; neither inequality is claimed proved.

`INCIDENCE_WASTE_EXCHANGE.md` records the complementary direct-tree route. It
proves the exact basis-exchange formula

```text
Delta W = 3(new unsupported endpoints - removed degree-one endpoints)
```

and the resulting saturation condition for a `W`-minimum dual tree. It also
rejects two proposed globalization steps: full boundary sides need not survive
in the complementary primal tree, and a Hall condition counting only the
boundary-owning `H` components fails from width 17 onward. Retaining all `H`
components reduces the corrected Hall target exactly to
`Q_U+c_F+c_H>=n+4`, so the global congestion inequality remains open.

`residue_two_universal_bound_ledger.py` checks this algebra with integers and
collects the strongest currently verifiable scope without promoting finite
fits to a theorem.

## Proven scope

* Widths 5 and 8: complete reachable/completable row-frontier sources have
  minimum charged curvature 5. Their complete transition counts are imported
  from the regenerable structural-gap certificate.
* Width 11: an exact curvature-five witness falsifies contiguous packet support.
  At row 8 one component occurs in packet groups 1 and 3 but not group 2. It
  remains a valid width-one hull carrier and is repaired by the next row.
* Width 17: the committed exhaustive unmirrored search has no solution with at
  most 178 `U` vertices. Two cells before termination, all 20 surviving states
  have attachment debt 2, while 18 have merge capacity 1 and two have capacity
  0. No suffix closes. The 179-`U` positive control has debt 1, budget and merge
  capacity 1, and one closing suffix. This certifies the extra unit at `n=17`,
  not at arbitrary width.
* The fixed width-11 and width-14 patterns verify the equality identity, but are
  not represented as complete searches in this ledger.

## Unconditional attachment skeleton

The former `4/3/9` port-signature observation is not topological. Affine A23
has five repeated components, three cyclic runs per component, and twelve
compressed runs, violating two of those constants. Nested noncrossing boundary
words also give arbitrarily many repeated components without an `A,B,A,B`
crossing. The ledger no longer uses `4/3/9` as a coverage target.

The replacement metric first contracts cyclically adjacent ports of each
component. If component `i` has `r_i` occurrence runs, define

```text
branch_cost = sum_i (r_i-1).
```

The following bounds are unconditional:

```text
branching_components <= branch_cost
branch_cost <= perimeter_ports - ported_components = attachment_surplus.
```

The last term is exactly `q_s-d_s` in the centered-annulus identity
`M_s-(s-1)^2=(q_s-d_s)+beta_s`. Disjoint connected planar components also
cannot have alternating cyclic `A,B,A,B` boundary occurrences. These statements
do not imply curvature five.

Complete equality censuses give maximum branch cost zero on all 242 n5 paths
and at most one on all 704 n8 paths. Both n11 controls, including the silent
carrier gap, and the fixed n14 control also have maximum one. The silent n11
row retains branch cost one because occurrence runs remain separated across
empty packets. This bounded equality behavior is a conjecture beyond the stated
finite scope. Affine controls expose growth: A17 through A41 have maxima
`2,3,...,10`, with A23 equal to four.

Exact transition tests falsify all three naive row-local candidates
`weight>=Delta(debt)`, `weight>=Delta(branch_cost)`, and
`weight>=Delta(debt+branch_cost)` already in the complete n5/n8 corridors.
Any viable local potential therefore needs cap phase or remaining merge
capacity in addition to the reduced skeleton.

## Accounting identity and first defects

The synthesized four-term expression

```text
Phi = -3U + row + 2faces - 2debt
```

is now classified correctly as an accounting identity. The exact frontier rank
formula is `rank=faces-debt`, so every valid row transition satisfies

```text
weight + Phi(out) - Phi(in) = 0.
```

At a connected terminal, `Phi=-K(U)`. Thus evaluating `Phi=-5` at the old
baseline substitutes `K=5`; it does not derive the baseline. The symbolic
all-length check of the 19 stable rules remains useful counter verification,
but supplies no coercive inequality.

`residue_two_first_defect_certificate.py` separately performs an exact
first-entry monitor. No complete `n=5` path leaves the one-hull codec. At `n=8`,
the minimum path whose first codec defect has face-cut width two has curvature
eight, giving a defect gap of three above the curvature-five minimum. Every
codec-valid completable edge at these widths passes the bounded streaming
topology and local-counter certificate. This proves symbolic soundness for each
admitted word and a finite first-defect theorem. Arbitrary-word codec closure
and arbitrary-width coverage remain open.

An exact held-out `n=11` two-channel optimization strengthens this result.
There is no face-cut-width defect at U limit 72, while the first defective path
has 73 U vertices, curvature eight, and first width-two cut at row 7. The search
uses no beam or symmetry quotient and checks 22,022,977 transitions at the
73-U limit. Its replayable witness and scoped result are stored in
`residue_two_n11_face_cut_defect_result.json`.

The first-defect gap is not a future-capacity deficit. In the exact `n=8`
defect witness, the first width-two frontier has debt four and the final row
performs all four independent merges; the bound
`min(debt,remaining rank,active-edge capacity)` is attained. The `n=11` defect
suffix similarly discharges all six current debt units. Therefore no universal
`debt-1` or mandatory two-carrier merge penalty is valid. A proof must charge
the prefix/creation geometry and remaining cap weight instead. See
`FIRST_DEFECT_CAPACITY.md`.

The silent-hull topology checker is now normalized to a genuinely bounded cut
state. Irreversible actual-to-multiple-target incidence is rejected immediately;
every retained component is attached to one of four actual or three expected
ports, giving a hard bound of seven live components per side. It also enforces
top/interior/bottom frontier shape. This proves bounded symbolic soundness for
accepted words. The arbitrary-word completeness induction and preservation of
one-hull coverage remain separate obligations.

A scalar potential on this bounded state is impossible. Two established stable
rules repeat the same packet-cut state with dominant-packet weight `-1`, giving
the contradiction `-1+psi(q)-psi(q)>=0`. Exact finite CEGAR further rules out an
atom-occurrence sum and the next adjacent-bigram word model under tight equality
anchors. The richer finite-parser feature class is exactly infeasible as well:
two transformed constraints have opposite normals and exact nonnegative
multipliers reduce them to `-1>=0`. This is limited to the named state-only
parser class under tight `n=5,8` equality anchors. Incoming transition history
is not ruled out, but materializing that augmented product is paused after
exceeding the workstation memory budget.

## Cap/merge potential experiment

`residue_two_cap_merge_potential.py` tests

```text
weight + Phi(out) - Phi(in) >= 0
```

using six interpretable features: cap phase, active-face component deficit,
remaining merge-capacity surplus, previous-row U count, OUT-face count, and
branch cost. Remaining capacity is the maximum cumulative positive debt
reduction in the declared equality suffix language. This definition is exact
but finite-width; it is not yet a local formula.

All 588 equality-corridor transitions at n5/n8 project to 268 exact difference
constraints on 133 states. The synthesized integer potential makes every edge
tight and has terminal constant five. Removing cap phase or merge-capacity
surplus creates incompatible projected potential classes. Branch cost is
redundant on this finite pool but remains in the state so silent-separated
occurrences are not identified by a contiguous-support assumption.

The fixed n11/n14 controls extend the system with 25 tight transitions. They do
not provide held-out coverage: each path has only two states known to the
training table and no fully known edge. The affine 179-U n17 path also extends
the constraints; sixteen rows are tight and one contributes slack three.

Thus this feature set supports terminal constant five on its complete training
scope, but not the n17 extra unit. The accepted n17 terminal is already a
trained potential-`-5` feature. Forcing potential `-8` would conflict with that
anchor. The final-two-cell artifacts supply the missing discriminator:

```text
unpayable_debt = max(rooted_debt - remaining independent merge capacity, 0).
```

All 178-U survivors have positive unpayable debt, with histogram `{1:18,2:2}`;
the 179-U control has zero. No committed backpointers connect this terminal flag
to the top cap, so it cannot yet be telescoped into an extra-unit proof. The
next obligation is a covered local upper bound for merge capacity plus a
persistent spent-merge or unpayable-debt flag.

## Persistent local debt

`residue_two_persistent_debt_certificate.py` replaces suffix-enumerated merge
capacity by a history channel carrying cumulative U and rank expenditure,
spent independent merges, created debt, and the maximum unpayable debt seen so
far. The last coordinate is monotone, so a later silent-carrier repair cannot
erase an earlier deficit.

At a row frontier the safe local upper bound is

```text
min(current debt, remaining graphic rank, 2 * remaining U budget).
```

Each term is unconditional: one merge pays at most one debt component, consumes
one rank unit, and every future U vertex exposes at most its left and upper
processed edges. In the final row, a two-state dynamic program exactly
maximizes active edges under the remaining U budget and previous-row cut mask.
It does not test suffix acceptance.

Lifting every complete n5/n8 equality edge produces 503 augmented histories,
225 projected features, and 783 transition observations collapsing to 350
exact constraints. All are tight with terminal constant five. Fixed n11/n14
controls retain zero persistent deficit and extend the system, but remain
single-path controls.

At the n17 final two-cell cut, the local active-edge bound exactly reproduces
the former exhaustive suffix capacities: the 178-U states have unpayable-debt
histogram `{1:18,2:2}`, while the 179-U replay has debt and capacity one. Thus
terminal separation no longer depends on suffix enumeration. The positive
control is evaluated with budget 179; evaluating it against 178 would correctly
mark budget exhaustion rather than prove impossibility at 179.

This yields a finite-language theorem only: constant five holds on the complete
augmented n5/n8 languages, silent hulls are allowed, and all represented n17
178-U terminal states reject. It does not reject equality for every `k>=5`.
The committed 178-U dump has no predecessors, so its persistent history cannot
be reconstructed to the top cap. Global completion requires either a symbolic
silent-hull transition lemma for every `K<=5` packet or a regenerated n17 search
that stores predecessor summaries for this channel.

## Missing lemma

The smallest useful coverage target only needs to classify low curvature:

> For every `n=3k+2` and every dual-connected `U` with `K(U)<=5`, every row
> frontier admits an OUT-rooted width-one hull carrier, allowing silent passage
> through unoccupied packets, and every packet/cap update belongs to a finite
> symbolic language whose minimum accepting min-plus weight is 5.

This combines coverage, a finite transition certificate, and a noncircular
minimum-accepting-weight theorem. All three parts are necessary. The n11 test prevents
replacing hull support by the false contiguous-support condition.

After this lemma, the attachment obligation is to show that every `K(U)=5`
candidate for `k>=5` eventually has rooted attachment debt larger than all
remaining merge capacity. The n17 terminal artifact proves one instance only.

Regenerate and test with:

```bash
python3 -B -m analysis.residue_certificates.residue_two_universal_bound_ledger \
  --output analysis/residue_two_universal_bound_ledger.json
python3 -B -m analysis.tests.residue_certificates.test_residue_two_universal_bound_ledger
```

## Direct-program execution update

The expanded direct proof attempt is summarized in
`DIRECT_PROOF_EXECUTION_STATUS.md`. It proves exact boundary-peeling,
multi-edge exchange, radial-merger, and maximal-counterexample lemmas, but also
finds counterexamples to every tested scalar globalization. The revised
construction search likewise finds a one-hidden-component obstruction in all
closest exact-charge open-slab interfaces and no 333-U repair in more than 49
million bounded candidates. Consequently the arbitrary-width universal bound,
defect-three tail, and revised construction remain open and are not promoted
from finite certificates to theorems.
