# Step 10: reverse forced frames

This note records only symbolic construction facts. Search states and finite
certificates are not used as induction hypotheses.

## Formal interface

`GridGraphs/ReverseFrame.lean` defines `ReverseFrameTemplate`. A template
contains:

- a coordinate embedding of the old forced set;
- acyclicity of that embedded core in the **new** ambient grid;
- a duplicate-free, core-disjoint ordering of the new frame;
- exact coverage and cardinal gain; and
- `SequentiallyInsertable` for the frame ordering.

The core condition is deliberately stronger than acyclicity in the old grid.
An old forced boundary vertex acquires new incident edges after widening, so an
arbitrary adjacency-preserving embedding does not transport the forced forest.
The theorem `ReverseFrameTemplate.newForced_isAcyclic` obtains successor
acyclicity from the sequential insertion equivalence.

## Residue one

Put `N = 3(k+1)+1`. Shift every old coordinate down by three rows:

```text
(r,c) |-> (r+3,c).
```

The row classes and the exceptional final and bottom rows then align exactly.
Consequently every forced vertex in the old complement remains forced in the
successor complement. The difference is coordinate-defined as

```text
forcedResidueOne(k+1) \
  image(residueOneReverseEmbedding(k), forcedResidueOne(k)).
```

It consists geometrically of the forced positions in the new top three rows
and the three new right columns on shifted rows whose row type is forced there.
The formal cardinal calculation gives

```text
|F(k+1) \ image F(k)| = 2N,
|F(k+1)| = |F(k)| + 2N.
```

This is implemented in `GridGraphs/ResidueOneReverseFrame.lean`. The current
template reconstructs `SequentiallyInsertable` from the already proved,
uniform symbolic residue-one acyclicity theorem. Thus it proves the exact
reverse-frame factorization without finite certificates, but it is not yet an
independent inductive proof of acyclicity. An independent proof must verify the
insertion conditions for a geometric ordering of the top rows and right-column
extensions.

## Residue zero

The forced count is

```text
|F_0(k)| = (3k)^2 - (6k^2-3k+2) = 3k^2+3k-2,
|F_0(k+1)|-|F_0(k)| = 6k+6 = 2(3k+3).
```

The phase word itself has the successor decomposition

```text
B_(k+1) = R_(k-2) S_(k-2) B_k R_k,
```

so old phase rows shift down two and gain three columns. This does not extend
to a single offset embedding of the complete forced set: the old empty top row
is entirely forced, while its two-row-shifted successor row is the new
`R_(k-2)` phase row and is not entirely forced. Therefore the residue-one
three-row offset argument cannot prove residue zero.

A residue-zero reverse frame must use one of these genuinely different moves:

1. a piecewise coordinate embedding that sends the two cap rows separately
   and shifts only the old phase block; or
2. a cap exchange: delete the old top-cap forced path, embed the persistent
   phase core, and sequentially reinsert both the replacement cap and frame.

The second formulation matches the existing persistent bounded-anchor work,
but `ReverseFrameTemplate` currently permits insertion only, not deletion and
reinsertion. No unconditional residue-zero template is claimed here.

## Residue two

The finite target counts have the required increments:

```text
n=14 -> 17: 110-77 = 33 = 2*17-1,
n=17 -> 20: 150-110 = 40 = 2*20.
```

These witnesses establish two finite endpoints only. Their moving seam does
not define a stable coordinate embedding, and the known `n=20` exact pattern's
naive three-row/three-column pump is formally disconnected at `n=23`
(`uResidueTwoExact_seven_not_dual_connected`). In addition, no target-count
`n=23` witness is currently known. Hence neither finite transition supports a
stable residue-two reverse recurrence. A stable claim requires a new
coordinate family whose embedded core is acyclic in the widened ambient grid
and whose `2N` frame has a uniform sequential ordering.
