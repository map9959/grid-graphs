# Boundary-conditioned fillings and the price of exterior identifications

## Model (2026-09-14)

Let G be a finite square-grid board, S a vertex region, and O its full
vertex complement. All vertices, including isolates, remain present. Fix
all F/U labels in O and a set B of mandatory F vertices in S. Other vertices
of S are freely chosen. Assume the baseline B, together with the fixed
exterior, has a forced forest. Every primal edge incident to F is forced.

Cycle rank of a finite quotient multigraph Q is
rho(Q)=|E(Q)|-|V(Q)|+c(Q), retaining loops and edge multiplicities.
Each edge keeps its physical endpoint provenance after contraction.

Keep every physical grid edge with at least one endpoint in S. A port is
an O vertex adjacent to S (one port per vertex, not per crossing edge).
Keep its coordinates and F/U label, and the partition pi of ports induced
by the actual induced exterior graph H[O]. Contract each exterior tree to
one root. Distinct crossing edges remain distinct, including parallel
edges after contraction. Components of H[O] without ports are retained
as a scalar c_out_closed. This is sufficient data for exact filling
feasibility: a filling is legal exactly when the contracted multigraph is
a forest. Outside labels and pi are fixed while the interior varies.

The analogous exterior partition for G[F] is required if one wants r
itself from the compressed signature. An H partition alone does not
determine carrier connectivity. The implementation below uses full-board
replay for the r,b,c ledger rather than conflating these partitions.

## Exact gluing

For a legal filling, write e_cross for forced crossing edges and a_cross
for F--F crossing edges. With all isolated vertices included in c,

    c_in + c_out = c + e_cross,
    r_in + r_out = r + a_cross.

Define b on each induced side by summing 4 minus induced grid degree
over that side's U vertices only.
If L is the number of primal cut edges, then

    b_in + b_out = b + 2L - e_cross - a_cross,
    K_in + K_out = K + 2L,     K = r+b+c.

Proof: each cut edge UU contributes two artificial hole units; FU
contributes one hole unit and one forced-component split; FF contributes
one carrier split and one forced-component split. Each case contributes
two. These identities use the whole complementary region, including
every crossing edge, rather than only a named terminal face.

## Uniform exterior-identification lemma

Fix physical ports, their labels, and B. Let pi' coarsen pi by q independent
root identifications (q = |pi|-|pi'|). Suppose B is feasible under pi'.
Let M(pi) be the maximum number of optional preserved vertices in S.
Then

    0 <= M(pi) - M(pi') <= 2q.

**Proof.** Splitting roots cannot create a cycle, so feasible fillings
under pi' are feasible under pi. Take an optimal forest under pi and
identify roots to obtain pi'. Each identification raises multigraph
cycle rank by at most one, so the resulting rank is at most q. If there
is a cycle, it contains an edge absent from the baseline graph, since
that graph is a forest by hypothesis. All its currently F endpoints are
optional vertices in S: a fixed F endpoint would force it in the baseline.
Change all of these endpoints to U, at most two vertices. The edge disappears.
Deleting edges cannot increase cycle rank, and deleting a cycle edge
decreases it by one. Repeat at most q times. The resulting legal filling
retains B and loses at most 2q optional vertices. This proves the bound.

The initial coefficient-one argument was withdrawn during this session:
removing one F label from an FF edge does not remove that edge. The exact
rank-penalty test below exposed this mistake, even though the initial
finite comparisons against the much larger discrete-port q all passed.

The baseline hypothesis matters: exterior forced attachments can already
make a cycle through an all-U interior. No optional deletion then repairs
it. Mandatory rail vertices cannot be used as deletable coupons.

This is a paper proof, not a Lean theorem. Independent mathematical review
in batch001 accepted the argument after the definition clarifications
recorded in `research_batches/BATCH_001_REVIEWS.md`. It is
uniform in region size and allows arbitrary admissible exterior
attachments; it is not a constant-gap upper bound. The quantity q is a
connectivity rank, not a new component credit. It cannot be charged both
here and in the root-restoration ledger of the existing metric paper.

### A simple obstruction on an actual grid exterior

On a 3-square take S={(1,1)}, no mandatory interior F, and the single
exterior F vertex (0,0). The baseline is a two-edge corner star plus
isolates. Its north and west ports are connected outside; its east and
south ports are separate. Thus q=1 relative to the discrete partition.
Preserving the center makes the four-cycle

    (0,0)--(1,0)--(1,1)--(0,1)--(0,0).

Consequently M(actual)=0 and M(discrete)=1. Even one exterior
identification can matter.
The relaxed center filling is not a feasible full-board witness.

### Exact rank-penalty form and maximum-specific consequence

Let X range over fillings feasible under the finer partition pi. Let
rho(X) be the cycle rank after imposing pi', and let |X| count optional F.
The same deletion proof gives the exact identity

    M(pi') = max_X (|X| - 2rho(X)).

Indeed each term is at most M(pi') by repair, while an optimum under pi'
belongs to the range and has rho=0. In particular, for any filling X0
optimal under the actual exterior, every relaxed forest X satisfies

    |X| - |X0| <= 2rho(X).

Conversely these inequalities imply actual local optimality, by applying
them to all actual feasible fillings, whose rho is zero. This is an exact
maximum-specific certificate, not a heuristic local-search condition.
It can give a sharper price than 2q for a particular proposed replacement.
The cycle rank must be recomputed for the actual quotient graph: a list
of cycles in a previous filling, or a bank-incidence cycle count, is not
this quantity.

Exactness concerns the maximum over fillings, not a claim that each
individual candidate requires exactly 2rho deletions.

This rank penalty does not by itself pay height-weighted terminal loads.
Summing it independently over windows can charge the same exterior tree
several times. A common cut and a non-reusing rank allocation are still
needed before applying it to the global upper-bound program.

### Coefficient two is sharp for root refinements

The complete 4-square run found `exterior_301`. Its baseline, with
S=[1,3]x[1,2] initially all U, is

    .U..
    UUUU
    .UUU
    UU.U

The actual ordered port blocks (row-major vertex indices) are
{1,2,3,4,8} and {13,14,15}. No optional vertex can be preserved: the
exact optimum is zero. The relaxed candidate preserving vertices 6 and 7 is

    .U..
    UU..
    .UUU
    UU.U

Its full forced graph has cycle rank one, with the square 2--3--7--6--2.
Both 6 and 7 must be made U to break its middle FF edge: the other three
edges remain forced by the exterior F vertices 2 and 3. This refutes the
one-unit rank-penalty formula on an actual grid exterior.

More precisely, split only port 3 off the first block. Under that finer
partition the exact optional optimum is two; restoring this single root
identification makes it zero. Both baseline quotient graphs are forests.
Thus the coefficient two in the uniform partition-refinement lemma is
sharp. The finer partition is an abstract edge-deletion relaxation, not
another realizable exterior with those same fixed labels. The coarse
partition and its cyclic candidate have explicit grid realizations.

## Partial moving-interface experiment

Use the actual rails (35) in PAPER_CLEAN_ALLOCATION.md with L=1, R=7,
y_0=1, t=1 on a 9-square, and a_0,a_1 in {2,3,4}. Free a rectangular
seam S = [2,5] x [2,4], retaining every rail vertex in S as mandatory.
Thus the endpoints, gap, and arbitrary optional additions inside S are
optimized, with the complementary rail pieces kept as actual exterior
components. Enumerate all fillings, both for the actual exterior partition
and its discrete-port relaxation. Also consider every feasible one-vertex
addition to the exterior skeleton. These are complete instances of this
specified family, not all exteriors and not a fixed-width asymptotic claim.

A second complete experiment uses every exterior labeling around a 3x2
region S=[1,3]x[1,2] in the 4-square. It compares every interior filling
with an independent literal full-board traversal. This includes a physical
boundary; the moving-seam experiment is strictly interior.

Success criterion: verify exact gluing and test the uniform rank price;
in particular test whether the stronger zero-price rule (forget outside
connectivity when optimizing a seam) is false on an actual exterior.
Any abstract relaxed optimum is explicitly distinguished from a realizable
full-board witness. Neither experiment searches above side 9.

## Completed results

| Family | Feasible baselines | Fillings checked | Legal fillings | Cases with positive connectivity price | Maximum price |
| --- | ---: | ---: | ---: | ---: | ---: |
| All 4-square exteriors around the chosen 3x2 region | 576 | 36,864 | 2,278 | 523 | 3 |
| One-step 9-square moving seams and single exterior additions | 279 | 189,056 | 308 | 246 | 4 |

All 1,024 four-square exterior labelings were considered. The 448 rejected
baselines already contain cycles, so no addition can make them feasible.
The Rust test also checks this rejection against every full 4-square
labeling. Every accepted baseline has every optional subset enumerated;
there are no time/node cutoffs or sampled interiors.

The maximum seam price is attained already by `seam_3_2_outside_None`:
actual optional optimum zero versus discrete-port optimum four. This is
an interior moving-interface instance with multiple actual exterior
components. It shows that a free-connectivity optimum is unusable even
for this short seam. Its sparse exterior has many unused components,
including 35 portless exterior components. It is not a low-K or
positive-excess counterexample to the global conjecture.

An independent Python adjacency-traversal program re-enumerated all
225,920 fillings from the saved cases, confirming both optimum counts,
both feasible counts, and the corrected factor-two rank-penalty identity.
Fourteen four-square exteriors violate the attempted unit-rank penalty;
none of these seam instances do. Absence in the seam family is finite
evidence only. The refined-partition sharpness case has its own Rust
exhaustive test.

Validation: Rust library suite **48 passed, one pre-existing expensive
test ignored**. No Lean changes or verification were performed. The
proof above subsequently passed the independent mathematical review in
batch001; that review did not rerun these earlier finite experiments.

### Artifacts and reproduction

* `src/boundary_conditioned.rs`: exact outside roots, exhaustive fillings,
  whole-cut ledger checks, factor-two penalty check, and regression tests.
* `src/bin/boundary_conditioned.rs`: specified finite families, complete
  case output; refuses to overwrite an existing output.
* `analysis/interface_fillings/audit.py`: independent adjacency traversal
  and exhaustive replay of every archived case.
* `data/boundary_conditioned_20260914.json`: frozen case data, SHA256
  `634c65a359a49edec79e36a942a2f835292cb61893011a03ff2827350a0557cf`.
* `data/boundary_conditioned_20260914.audit.json`: independent results,
  largest-price examples, and the first unit-price counterexample.

The frozen case data was generated before adding the stronger rank-penalty
assertion, which exposed the false coefficient-one proof. The corrected
tests and independent audit re-enumerated the cases afterward; the data
itself was not changed.

```bash
cargo test --lib -- --test-threads=2
cargo run --release --bin boundary_conditioned -- /tmp/opencode/interface-reproduction.json
python3 -m analysis.interface_fillings.audit /tmp/opencode/interface-reproduction.json /tmp/opencode/interface-reproduction.audit.json
```

## Consequence for the next mathematical step

The replacement inequality applies to a UNION of windows using one
common complementary graph and one actual cycle rank. Adjacent windows
keep their connecting edges; disconnected windows may share actual outside
roots. If a relaxed simultaneous replacement gains Delta optional F and
its actual quotient has rank rho, then it has a feasible repair gaining
at least Delta-2rho. Consequently

    Delta > 2rho  =>  the original board was not a maximum.

This is a uniform compositional local-extremality test with arbitrary
outside attachments. Artificial cuts still use K_in+K_out=K+2L, and the
rank is measured once after all replacements, rather than separately
charging each window's escape components. It removes a connectivity
assumption from the *replacement test*, not from the existing global
metric upper theorem.

The next substantive target is to construct such a simultaneous challenger
from an unpaid partial moving interface in a hypothetical low-K maximum:
prove that its gain exceeds twice the common rank after the already-used
singleton/isolate resources and the height-weighted demand are accounted
for. The current oracle supplies exact counterexample tests for that
claim. It does not yet supply the challenger, a global non-reusing window
decomposition, or a bound on the total rank.

There is no self-renewing geometric pump here. Repeating these sparse
local obstructions is not evidence of an asymptotic excess construction.
The reviewed unconditional bound remains T+floor(k/2)+1; the constant-gap
upper and constant-gap lower remain open.

Follow-up: `INTERFACE_REPLACEMENTS_14.md` records 5,132,288 complete
replacement fillings on actual near-optimal boards. Generic selected
windows found no gain; trace-informed controls recover existing gains.
A complete single-supplier test isolates one useful boundary terminal,
and an actual-tree path certificate shows that a neutral core repair
separates its prospective edge endpoints without changing total c.
