# Astra Roadmap: Exact Square-Grid Optimum

Updated: 2026-09-05.

This is the new working roadmap. `ROADMAP.md` and `ROADMAP_OLD.md` retain
the previous programs, evidence, and failed approaches for reference. Their
task ordering is not binding. Reuse valid mathematics, not accumulated workflow.

## 1. Goal And Completion Criterion

For a spanning tree of the n by n grid, a preserved vertex retains its full
grid degree. Let `P(n)=maxPreserved n n`.

The conjectured formula, for n >= 3, is

```text
P(3k)   = 3k^2+3k-2,     k >= 1,
P(3k+1) = 3k^2+5k,       k >= 1,
P(3k+2) = 3k^2+7k+1,     1 <= k <= 4,
P(3k+2) = 3k^2+7k,       k >= 5.
```

The active research focus is residue two. A solution requires an unconditional
upper bound and a feasible construction attaining it. Conditional assembly,
an abstract tree with the right count, and finite examples are not solutions.
The formula itself remains open to revision if mathematics contradicts it.

## 2. What Is Actually Available

| Result | Status |
|---|---|
| Maximum preserved vertices equals maximum feasible forced-set size | Established in Lean |
| Exact component and boundary ledgers | Established in Lean |
| Exact bases P(3)=4, P(4)=8, P(5)=11 | Established in Lean |
| Residue-zero and residue-one matching lower constructions | Established in Lean |
| Residue-two target-score lower witnesses through n=20 | Established in Lean |
| Uniform affine residue-two lower bound `3k^2+6k+5`, k>=5 | Established in Lean |
| General sharp square upper bounds | Still open |
| Residue-two target lower family for k>=7, starting at n=23 | Still open |
| Five-unit boundary bound and counter-skeleton obstruction below | Paper deductions; not yet new Lean theorems |
| Full formula assembly | Established only conditionally |

Residues zero and one are complete on the construction side, not yet as
unconditional arbitrary-width exact formulas. A residue-two-specific proof
need not wait for the common upper theorem; a full diagonal result still
needs the other residues' upper bounds.

These are source-status statements, not a fresh full-build certification.
Do not infer current build success from historical build counts.

## 3. The Central Model

For any set F of grid vertices, put `U=V\F` and let H contain every grid
edge incident to F, on the full grid vertex set. Then

```text
F feasible <=> H acyclic.
P(n) = max_(F feasible) |F|.
```

A feasible H need not be connected: it extends to a spanning tree. Define

```text
f = |F|,
r = number of components of grid[F],
c = number of components of H, INCLUDING isolated U vertices,
b = sum_(u in U) (4-deg_grid(u)),
B = r+c+b.
```

Corners in U contribute twice to b. The established component ledger gives

```text
3f+B = n^2+4n.
```

For n=3k+2 the entire residue-two conjecture becomes

```text
min_(F feasible) B = 3k+9,    1 <= k <= 4,
min_(F feasible) B = 3k+12,   k >= 5.
```

This is an exact reformulation, not an upper-bound proof. It puts construction
and obstruction on the same accounting system and permits a direct proof
instead of making the historical contour-routing pipeline mandatory.

## 4. New Deductions

Detailed paper proofs and qualifications are in
`analysis/RESIDUE_TWO_COMPONENT_BUDGET.md`.

### Boundary Budget

Every feasible F on a square of side n>=5 satisfies `b>=5`.

At each corner, its two boundary neighbors cannot both be F: they would force
the corner unit-cell cycle. The four disjoint pairs therefore require four
noncorner boundary U vertices. If b<=4, these are the only boundary U vertices
and none are adjacent when n>=5. Every perimeter edge would then be forced,
again a cycle. This proves the fifth unit is necessary.

For n>=6, equality b=5 forces exactly one perimeter UU edge. The other
perimeter edges form a path through every boundary vertex in H. This is a
useful necessary boundary condition for b=5 constructions, not a proof that
optimal constructions must have b=5.

### Component Obstruction

At stable target size `f=3k^2+7k`, the ledger and `c>=1,b>=5` imply

```text
r+c+b = 3k+12,
r <= 3k+6.
```

Consequences:

- The proposed counter skeleton with `4k+1` distinct maximal preserved
  components is impossible for k>=6, hence throughout its intended k>=7 range.
- Retaining `4k` distinct components at target count is impossible for k>=7.
- At n=23 the target permits at most 27 components. The counter proposal has
  29, and the audited affine architecture has 28.
- The average maximal preserved interval length at target is at least
  `(3k^2+7k)/(3k+6)>k`. A bounded-island construction cannot work uniformly;
  tile segments must concatenate into long components if tiles are used.

The abstract counter tree and its summed lengths remain arithmetically valid.
Their intended grid realization does not. Merging labeled intervals changes
the skeleton; overlapping them requires recounting the preserved set.

### Successor Budget

The uniform affine score has `B=6k-3`. The stable target has `B=3k+12`.
Thus the affine deficit is k-5 preserved vertices, or `3(k-5)` budget units.

```text
Exact successor:  Delta f=6k+10, Delta B=3.
Affine successor: Delta f=6k+9,  Delta B=6.
```

A viable new successor must address component/boundary growth, not just add
one more preserved vertex to an unchanged incidence architecture.

## 5. Immediate Formal Milestone

Certify the new obstruction before investing in another construction grammar.

1. Prove the opposite-neighbor restriction from the unit-cell cycle: a vertex
   has at most two F-neighbors, and two must be opposite. Recover straightness
   of maximal preserved components using existing results where possible.
2. Prove `b>=5` for n>=5 and the single-perimeter-gap equality case for n>=6.
3. Combine with the existing ledger to prove `r<=3k+6` at target count and the
   exclusions for `r>=4k` and `r>=4k+1` in the stated ranges.

Deliverable: checked unconditional Lean statements about actual grid sets,
not assumptions about an abstract incidence graph. These are supporting
theorems, not completion of either sharp bound.

## 6. Lower Track: Geometry With The Right Budget

The next research deliverable is a coordinate-defined target family or a
coordinate-defined successor with a provable invariant. Design coordinates
and topology together. Do not require an abstract skeleton to be completed first.

Every candidate must specify and justify f, r, c, b. Reject it immediately if
the ledger fails. Track isolated U vertices explicitly: an interval-incidence
tree may be connected while H has many isolated vertices.

Allow nonlocal rearrangement, deletion or merging of old components, and a
growing interface of ordered interval identities and attachment ancestry.
There is no requirement that every old interval remain a distinct successor
node. A merger that closes an old attachment path must identify the physical
connection removed or rerouted. A parent label alone does not establish this.

An optional sharply specified design class is

```text
b=5, c=1, r=3k+6, f=3k^2+7k.
```

Here H itself is a spanning tree. Its boundary contains the perimeter path
from the equality lemma. If u_j counts U vertices with j F-neighbors, then

```text
u_0=0, u_2=3k+5, u_1=6k^2+2k-1.
```

Its successor would have `Delta r=3`, `Delta u_2=3`, and `Delta u_1=12k+8`.
This is a conjectural sufficient class. No base in it is asserted to exist.
Failure of this class is not failure of the formula: permit other c,b splits
with the same total budget.

Completion gates:

1. Explicit coordinates for all sufficiently large k, with any omitted finite
   bases supplied separately; no interpolation from a few witnesses.
2. Exact cardinality and component/boundary accounting.
3. Uniform forced acyclicity or complementary dual connectivity, with actual
   grid attachments and no accidental cycles or reused physical connectors.
4. Lean construction and discharge of `RemainingMatchingDiagonalConstructions`.

## 7. Upper Track: Prove The Minimum

The direct targets are `B>=3k+9` for 1<=k<=4 and `B>=3k+12` for k>=5,
for every feasible F. The known lower witnesses then close the early range
and k=5,6; the lower track must close the remaining tail.

There are two live routes, with no predetermined winner:

**Direct interval geometry.** Contract maximal preserved intervals. Each U
connector joins at most two intervals, through opposite grid neighbors.
Retain physical connectors and any parallel edges when testing a candidate:
two connectors between the same intervals are already a cycle.

For an interval J, let N(J) be its neighbors in U and put `q(J)=|N(J)|-1`.
For a subfamily A define integer slack

```text
delta(A)=|union_(J in A) N(J)|-sum_(J in A) q(J).
```

For candidates with straight maximal components, feasibility is equivalent
to `delta(A)>=1` for every nonempty A. Equivalently, interval tokens admit a
matching after any one chosen U vertex is forbidden. The matching may depend
on that vertex. Tight overlapping families have an exact uncrossing rule.

These are forest sparsity identities, not the missing inequality. The actual
research gate is a grid-geometric argument forcing a deficient family at a
forbidden score, or a geometric classification of low-budget feasible sets.
In particular, the k=5 threshold still needs an explanation.

**Global contour exchange.** Retain the existing occurrence-preserving
physical exchange route as an alternative. Prove the missing expansion,
instantiate `UniversalPrimalContourRouting`, obtain universal waste, and then
prove the two residue-two exclusions. Do not assume the disproved regional
first-ownership certificate or count repeated contacts as new resources.

A direct proof of the budget minimum can bypass this route. Conversely, a
valid contour proof need not be rewritten in interval language. More generic
Hall or routing interfaces without new grid geometry are not a milestone.

## 8. What Is Superseded

- The counter subdivision is no longer an active uniform realization candidate.
- Abstract target length plus an abstract tree is not an adequate lower gate.
- A fixed injective old-interval embedding is not a construction requirement.
- Connected incidence is not necessary for forced-set feasibility.
- The historical regional first-ownership theorem is false in general, not an
  unfinished lemma to assume or complete unchanged.
- Exhausted local grammars do not forbid nonlocal constructions, arbitrary
  other periods, or new arguments. Their counterexamples retain their stated
  scope; no global impossibility follows merely from accumulated failed searches.
- New paper deductions are not formal theorems until checked in Lean.

## 9. Laptop And Verification Rules

This work runs on a laptop with 32 GB RAM and a short interactive time budget.

- No new exact-grid optimization, exhaustive enumeration, SAT/SMT, or expanding
  state-product search above 15x15. Reuse existing larger results.
- Being at most 15x15 is not permission for a long run. A proposed search needs
  a precise falsification question, explicit time/memory caps, and approval.
- Prefer symbolic reasoning. No optimization was needed for the new deductions.
- Polynomial replay of an explicit witness is different from finding an
  optimum. Keep even those checks short and purpose-specific. Finite replay
  is debugging evidence, not an arbitrary-width proof.
- Do not add another solver or generic proof framework without a concrete need.
- Preserve concurrent worktree changes. Do not infer verification from a clean
  file or an old status document.

During formal development, run the affected module from `lean/`:

```bash
lake env lean GridGraphs/NewModule.lean
```

Before reporting a formal milestone, run `lake build` from `lean/` and
`git diff --check` from the repository root. Audit new proofs for `sorry`,
`admit`, additional axioms, and computational proof dependencies. Report any
build or resource blocker explicitly. Documentation-only updates do not require
a full Lean build and must not be reported as one.

## 10. Minimal Navigation

| File | Role |
|---|---|
| `analysis/RESIDUE_TWO_COMPONENT_BUDGET.md` | New paper proofs, exact qualifications, analytic gates |
| `lean/GridGraphs/ForcedMaximum.lean` | Exact optimization equivalence |
| `lean/GridGraphs/ComponentReduction.lean` | Existing exact ledger |
| `lean/GridGraphs/SmallDiagonalExact.lean` | Structural small-grid proofs |
| `lean/GridGraphs/ResidueTwoAffineMax.lean` | Uniform near-target lower bound and exact deficit |
| `lean/GridGraphs/IntervalStarGluing.lean` | Reusable lower-bound acyclicity interface |
| `lean/GridGraphs/UniversalPrimalContourRouting.lean` | Alternative upper-bound endpoint |
| `lean/GridGraphs/DiagonalUpperResidue.lean` | Precise open upper hypotheses and adapters |
| `lean/GridGraphs/DiagonalFormula.lean` | Remaining construction obligation and conditional assembly |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Detailed source/evidence indexes, not substitutes for fresh verification |

Start with these files. Consult historical notes only when their specific
construction, obstruction, or interface becomes relevant; do not survey the
entire experiment collection.
