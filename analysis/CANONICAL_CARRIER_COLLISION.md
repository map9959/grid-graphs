# Canonical Carrier Collision

## Result

The exit-free canonical shore forest does not universally admit the proposed
collision discharge. Two distinct canonical roots can contact the same
cotree-free component even when there is no internal support-support tree edge
and no later exit in the current forest.

This does not refute a redesigned first-exit routing. It proves that such a
routing must change the forest before maximal shores are selected as roots.

## A 3 by 3 Example

Write `(i,j)` as `ij`. Let `T` contain

```text
00-01  00-10
01-02  02-12  12-11  12-22
10-20  20-21
```

This is a spanning tree. The omitted grid edges are

```text
01-11  10-11  11-21  21-22.
```

Hence the cotree support and free set are

```text
U = {01,10,11,21,22}
F = {00,02,12,20}.
```

The induced free components are

```text
{00}, {20}, {02,12}.
```

No tree edge has both endpoints in `U`, so the internal-edge resource is empty.

For the row sweep, the unsupported row/corner demands launch the chains

```text
row 0: 00->01
NE:    02->12 -> 01->02 -> 00->01
row 2: 20->21 -> 10->20 -> 00->10
SW:    10->20 -> 00->10.
```

Thus the maximal canonical roots are the distinct darts `00->01` and
`00->10`. Their physical root edges both contact the free component `{00}`.
They lie in different parent-forest components, so there is no earlier merger
between them. The current canonical forest also defines `exits := empty`.

Its two merger slots use physical child edges `01-02` and `20-21`. Therefore
the four terminal tokens map as follows:

```text
root   00-01 -> component {00}
root   00-10 -> component {00}
merger 01-02 -> component {02,12}
merger 20-21 -> component {20}.
```

There are four terminal tokens but only three free components and no internal
edge. Consequently `CanonicalTerminalResources` and
`CanonicalTerminalCollisionRouting` both fail for this exit-free realization.

## Formal Accounting

`TerminalCarrierQuotientRouting.lean` now separates any injectively labelled
family of physical tree-edge tokens into:

1. internal tokens, which reserve their physical internal edges;
2. one representative of each noninternal carrier class, which reserves that
   free component;
3. labelled collisions, consisting of all remaining contacts with already
   reserved carrier classes.

The only residual datum is an embedding of those collision labels into the
internal edges and free components left after both canonical reservations.
This factorization is exact: quotienting carrier contacts does not create new
capacity.

## Correct Next Target

The existing canonical parent chains are finite and deterministic, but the
repository does not yet assign a continuing chain to a specific split-outer
port. The next geometric construction must therefore provide all of:

1. a typed split-outer port used by each later boundary contact;
2. a first-contact truncation that makes those contacts roots;
3. injectivity and disjointness from direct exits;
4. restriction to the channel states below those first stops, so unused upper
   shore ancestors do not become spurious roots;
5. residual collision routing for the non-exit terminal tokens.

The first missing primitive is the port-valued continuation rule. A generic
finite `firstWhere` definition would prove termination but would not identify
which contour side incidence the channel actually uses, and therefore would
not advance global nonreuse.
