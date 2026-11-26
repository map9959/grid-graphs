# A length-dependent boundary charge without a frame hypothesis

Put the physical rim at `x=0`, and consider `H` consecutive rows of the
strip `0≤x≤d=3l`, `l≥1`. The **backing column** is `x=d`; its marks are
free. Write `M` for marks in columns `0..d-1`, `J` for holes on the
backing column, `b` for holes at `x=0`, and `I` for marked incidences
on the two short ends (including their corners). Write `B` for rows
whose `d+1` bits differ from `#..#..…#`. Then for **any forest**,

```
9*(M-lH) + B + 3b ≤ 6J + 3I.                         (1)
```

It is important that the term `J` is measured, not assumed zero.
Both the length and the depth can grow. This applies in particular
to forests avoiding every aligned frame.

**Proof.** In the strip let `R` be the number of straight marked runs
and `c` the number of forced components, counting isolates. The edge
ledger applied to the `M+H-J` marks gives the identity
`3(M-lH)=2J-b+I-R-c`. A nonordinary row pays either a marked-run
start in its three-row neighborhood or an isolate on the row itself.
Indeed, in three start-free rows there is no horizontal marked run
of length at least two: its leftmost mark cannot inherit from above
by diagonal exclusion. Every mark thus inherits vertically, so the
row masks are nested `A⊇B'⊇C`. The marks of `A` also occur in the
preceding row, and are spaced at least three (spacing two forces two
joins). If there is no middle isolate, the radius-one neighborhoods
of `A` cover the width. In width `3l+1` this forces exactly the
ordinary pitch phase, and dropping a center in `B'` leaves a lateral
neighbor uncovered. This includes the end rows by padding with empty
rows, which add only leaves to marks and cannot cover an unmarked
end site. A run start is billed by at most three middle rows. Hence
`B≤3R+c`. Substitute in the identity to obtain (1).

**Why this prices a defect in the square.** In a full-length strip,
erase its `M` marks and plant `l` complete bars at `0,3,…,d-3`.
Their stars are pairwise disjoint and disjoint from every retained
star in `x≥d`. This is a physical forest gaining exactly `ln-M`.
For a proper interval keep its first row empty at an internal start,
and the last two rows empty at an internal end. Each planted run can
attach at most once, via its own center at the single-blank end.
The loss in the replacement is at most `3l` per interval. Multiple
disjoint intervals on the same side can be replaced together with
these buffers. Different strips cannot simply bill the same sites.

In particular every unrestricted maximizer has `M≥ln` on a full
side. For `m` distinct rows with a guarded hole in the depth-three
bar, every `d=3l≥3` has `B≥m`. Since `I≤2(d+1)`, summing (1) proves

```
6 Σ_{l=1..q} J_{3l} ≥ q(m + 3b - 15 - 9q),       1≤q≤(n-1)/3.
```

Thus a linear number of such boundary defects in a maximizer forces
quadratically many omissions in the aligned interior columns (take
`q` near `m/18`). This is a propagation statement about omissions;
it does not charge each of those omissions separately to the sector
budget.

## Sharper tariffs at fixed depths, for every length

Let `B₀` count rows whose **first `d` bits** are nonordinary. The exact
integer transfer verifies

| depth | all-length inequality |
|---:|---|
| 3 | `30*(M-H) + 10 B₀ - 20 J ≤ 70` |
| 6 | `30*(M-2H) + 6 B₀ - 24 J ≤ 126` |
| 9 | `30*(M-3H) + 3 B₀ - 30 J ≤ 183` |

The frontier retains the last row **including the backing bit** and
the partition of its physical sites. A transition tries every new
row, rejects diagonal pairs or forced cycles, and adds the integer
weight on the left. Starting from the empty frontier, the verifier
computes an integer potential and checks `potential[v] ≥ potential[u]
+ weight` on every arc. This proves the price at unbounded length;
no periodicity or clean terminals are imposed. Depth six uses 941
states and 20,595 inequalities.

**Test against the linear gap.** For `n=3k+1` let
`r=(3k-13) mod 10`. Thirty times the deep unrestricted sector upper
minus thirty times `(comb+1)` is `k-26+3r`. The depth-six replacement
therefore excludes a gain over the comb as soon as, on even one side,

```
6 B₀ - 24 J - 126 > k - 26 + 3r.                       (2)
```

In particular `B₀-4J ≥ (1/18+ε)n` suffices at all sufficiently
large sides, for any fixed `ε>0`. For a maximizer the stronger
structural restriction `B₀≤4J+21` holds, even when `(2)` does not.

The physical stress test plants an off-phase mark at column two in
the straight part of the comb, deleting all old marks within distance
two first. This destroys both aligned-frame alternatives (one had
already failed in the perpendicular orientation). Repeating that
operation every nine rows gives extensive damage with only `O(1)`
holes at depth six, so (2) closes the gap for that pattern. At 193
the measured debit in thirtieths is `150`, above the required `65`;
the replacement actually gained 53 designated marks. One puncture
instead gives an all-size frame-avoiding forest only three marks below
the comb and `B₀,J=O(1)` on the perturbed side. Avoidance does not by
itself imply an extensive debit. The other unresolved possibility
is damage sustained by holes further inward.

The [sparse component exchange](SPARSE_COMPONENT_EXCHANGE.md) separately
prices the true component joins at holes and can restore punctured
three-column wings even when the strip debit above is nonpositive.

As a separate diagnostic, `interface_sector_test` added whole-side
maximality and the depth-three and depth-six prices to the deep sector
LP. It uses the exact three-bit mismatch and the two available three-bit
lower projections of a six-bit mismatch. The numerical optima at the
two normalization vectors tested were still `3648.166663` (side 103)
and `9034.833291` (side 163), within solver tolerance of the old real
uppers. This is not a rational certificate; these pooled marginal
constraints alone did not show a better unrestricted coefficient.

```
rustc --edition=2021 -O analysis/research_program/free_backing_price.rs -o target/free_backing_price
target/free_backing_price 3 10 20
target/free_backing_price 6 6 24
target/free_backing_price 9 3 30
python3 -B -m analysis.research_program.strip_debit_check
(cd lean && lake env lean GridGraphs/Geometry/BoundaryInterfaceDebit.lean)
```
